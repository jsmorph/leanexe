# /// script
# requires-python = ">=3.12"
# dependencies = ["torch==2.14.1", "transformers==5.18.0"]
#
# [tool.uv.sources]
# torch = { index = "pytorch-cpu" }
#
# [[tool.uv.index]]
# name = "pytorch-cpu"
# url = "https://download.pytorch.org/whl/cpu"
# explicit = true
# ///
"""Runs gpt.wasm's `forward` on the GPT-2 124M weights and compares it with Hugging Face's
GPT2LMHeadModel in float64.

Run with `uv run tests/gpt/gpt2_compare.py [path/to/gpt.wasm]`.  The script downloads the
pinned openai-community/gpt2 checkpoint, widens its float32 parameters to float64, and
writes the arrays `forward` takes to build/gpt2-124m/, one file of little-endian words per
array, with `c_attn` split into its `q`, `k`, and `v` columns and each of the sixteen
layer arrays stacked layer after layer.  For each prompt it compares every score; it then
generates greedily to 64 tokens, running `forward` on the whole prefix for each new token,
and checks each token against Hugging Face's choice for the same prefix.  Prompts stay
within 256 tokens, where `forward`'s allocation bound and the weights fit in 4 GiB of
WebAssembly memory.  The script fails if a score differs from Hugging Face's by more than
1e-12 of the largest score or if a token differs."""
import array
import pathlib
import struct
import subprocess
import sys
import time

import torch
from transformers import GPT2LMHeadModel, GPT2TokenizerFast

ROOT = pathlib.Path(__file__).resolve().parents[2]
HOST = ROOT / 'build/tools/leanexe-wasmtime-host'
WASM = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'build/gpt/gpt.wasm'
OUT = ROOT / 'build/gpt2-124m'
REPO = 'openai-community/gpt2'
REVISION = '607a30d783dfa663caf39e06633721c8d4cfcd7e'
NAMES = ['wte', 'wpe', 'g1', 'b1', 'wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo', 'g2', 'b2',
         'wfc', 'bfc', 'wproj', 'bproj', 'gf', 'bf']
MAX_TOKENS = 256
GENERATE_TOKENS = 64
LIMIT = 1e-12
PROMPTS = [
    'Hello, my name is',
    'The WebAssembly specification defines a portable binary code format and a text format '
    'for executable programs, together with a set of instructions that a virtual machine runs.',
    'Four score and seven years ago our fathers brought forth on this continent, a new nation, '
    'conceived in Liberty, and dedicated to the proposition that all men are created equal. '
    'Now we are engaged in a great civil war, testing whether that nation, or any nation so '
    'conceived and so dedicated, can long endure. We are met on a great battle-field of that '
    'war. We have come to dedicate a portion of that field, as a final resting place for those '
    'who here gave their lives that that nation might live. It is altogether fitting and proper '
    'that we should do this. But, in a larger sense, we can not dedicate -- we can not '
    'consecrate -- we can not hallow -- this ground. The brave men, living and dead, who '
    'struggled here, have consecrated it, far above our poor power to add or detract. The world '
    'will little note, nor long remember what we say here, but it can never forget what they did '
    'here. It is for us the living, rather, to be dedicated here to the unfinished work which '
    'they who fought here have thus far so nobly advanced.',
]
GENERATE_PROMPT = 'The meaning of life is'


def write_words(path, values):
    words = array.array('d', values)
    if sys.byteorder != 'little':
        words.byteswap()
    with open(path, 'wb') as file:
        words.tofile(file)


def flat(tensor):
    return tensor.detach().double().contiguous().reshape(-1).tolist()


def export(model):
    """Writes the arrays `forward` takes, unless the files for this revision exist."""
    stamp = OUT / 'revision'
    if stamp.exists() and stamp.read_text() == REVISION:
        return
    OUT.mkdir(parents=True, exist_ok=True)
    tr = model.transformer
    d = model.config.n_embd
    stacked = [[] for _ in range(16)]
    for layer in tr.h:
        w = layer.attn.c_attn.weight
        b = layer.attn.c_attn.bias
        parts = [layer.ln_1.weight, layer.ln_1.bias,
                 w[:, :d], b[:d], w[:, d:2 * d], b[d:2 * d], w[:, 2 * d:], b[2 * d:],
                 layer.attn.c_proj.weight, layer.attn.c_proj.bias,
                 layer.ln_2.weight, layer.ln_2.bias,
                 layer.mlp.c_fc.weight, layer.mlp.c_fc.bias,
                 layer.mlp.c_proj.weight, layer.mlp.c_proj.bias]
        for values, x in zip(stacked, parts):
            values += flat(x)
    arrays = [flat(tr.wte.weight), flat(tr.wpe.weight)] + stacked + [flat(tr.ln_f.weight),
                                                                    flat(tr.ln_f.bias)]
    for name, values in zip(NAMES, arrays):
        write_words(OUT / f'{name}.u64', values)
    stamp.write_text(REVISION)


def forward(config, ids):
    """`forward`'s scores for the token ids, as rows of `vocab` floats."""
    t = len(ids)
    nh = config.n_head
    eps = struct.unpack('<Q', struct.pack('<d', config.layer_norm_epsilon))[0]
    scores = OUT / 'scores.u64'
    args = [f'array-u64:{",".join(str(i) for i in ids)}']
    args += [f'file-u64:{OUT / (name + ".u64")}' for name in NAMES]
    args += [f'i64:{config.n_layer}', f'i64:{t}', f'i64:{nh}', f'i64:{config.n_embd // nh}',
             f'i64:{config.n_inner or 4 * config.n_embd}', f'i64:{config.vocab_size}',
             f'f64:{eps}']
    subprocess.run([str(HOST), 'call', str(WASM), 'forward', f'file-u64:{scores}'] + args,
                   check=True)
    values = array.array('d')
    values.frombytes(scores.read_bytes())
    if sys.byteorder != 'little':
        values.byteswap()
    if len(values) != t * config.vocab_size:
        raise SystemExit(f'forward returned {len(values)} scores for {t} tokens')
    return values


def argmax(values, start, count):
    best = start
    for i in range(start, start + count):
        if values[i] > values[best]:
            best = i
    return best - start


def main():
    model = GPT2LMHeadModel.from_pretrained(REPO, revision=REVISION,
                                            attn_implementation='eager').double().eval()
    assert model.config._attn_implementation == 'eager'
    tokenizer = GPT2TokenizerFast.from_pretrained(REPO, revision=REVISION)
    export(model)
    config = model.config
    vocab = config.vocab_size
    worst = 0.0
    for prompt in PROMPTS:
        ids = tokenizer(prompt)['input_ids'][:MAX_TOKENS]
        start = time.monotonic()
        ours = forward(config, ids)
        seconds = time.monotonic() - start
        with torch.no_grad():
            theirs = flat(model(torch.tensor([ids])).logits[0])
        largest = max(abs(x) for x in theirs)
        diff = max(abs(a - b) for a, b in zip(ours, theirs))
        worst = max(worst, diff / largest)
        print(f'{len(ids)} tokens: {len(ours)} scores in {seconds:.1f} s, largest {largest:.4g}, '
              f'largest difference {diff:.3g}')
    ids = tokenizer(GENERATE_PROMPT)['input_ids']
    total = 0.0
    while len(ids) < GENERATE_TOKENS:
        start = time.monotonic()
        ours = forward(config, ids)
        total += time.monotonic() - start
        t = len(ids)
        last = (t - 1) * vocab
        with torch.no_grad():
            theirs = flat(model(torch.tensor([ids])).logits[0, -1])
        largest = max(abs(x) for x in theirs)
        diff = max(abs(ours[last + j] - theirs[j]) for j in range(vocab))
        worst = max(worst, diff / largest)
        token = argmax(ours, last, vocab)
        expected = argmax(theirs, 0, vocab)
        if token != expected:
            raise SystemExit(f'token {t}: forward chose {token}, Hugging Face {expected}')
        ids.append(token)
        print(f'{t + 1} tokens in {total:.0f} s: {tokenizer.decode([token])!r}', flush=True)
    print(tokenizer.decode(ids))
    print(f'largest relative difference {worst:.3g}')
    if worst > LIMIT:
        raise SystemExit(f'difference above {LIMIT}')


main()
