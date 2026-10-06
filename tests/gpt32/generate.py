# /// script
# requires-python = ">=3.12"
# dependencies = ["torch==2.14.1", "transformers==5.18.0", "numpy"]
#
# [tool.uv.sources]
# torch = { index = "pytorch-cpu" }
#
# [[tool.uv.index]]
# name = "pytorch-cpu"
# url = "https://download.pytorch.org/whl/cpu"
# explicit = true
# ///
"""Generates text with GPT-2 124M in binary32, every step in the WGSL kernels of
Examples/Gpt32/Specs.lean, run by build/tools/leanexe-webgpu-host in session mode.

Run with `uv run tests/gpt32/generate.py [--driver swiftshader|llvmpipe] [--tokens N] [PROMPT]`,
or with `--export` to write the weight files and stop.
The script writes the pinned openai-community/gpt2 checkpoint to build/gpt2-32/ as Wasm arrays
of binary32 values (8 bytes per value), one file per array: the token embedding in four chunks
of at most 12,565 rows, the positional embedding, and each layer's arrays, with `c_attn` split
into its `q`, `k`, and `v` columns.  It runs Examples/Gpt32/Generate.lean, which writes the kernels,
sends the host the commands of `Examples.Gpt32.generate_host`, chooses each token with `greedy32`,
and saves the scores of each step.  For each step the script runs Hugging Face's float32 model on
the same prefix and reports the largest score difference relative to the largest score and
whether the two models choose the same token."""
import argparse
import os
import pathlib
import subprocess
import sys
import time

import numpy as np
import torch
from transformers import GPT2LMHeadModel, GPT2TokenizerFast

ROOT = pathlib.Path(__file__).resolve().parents[2]
HOST = ROOT / 'build/tools/leanexe-webgpu-host'
WGSL = ROOT / 'build/wgsl'
OUT = ROOT / 'build/gpt2-32'
REPO = 'openai-community/gpt2'
REVISION = '607a30d783dfa663caf39e06633721c8d4cfcd7e'
DRIVERS = {'swiftshader': '/usr/lib/chromium/vk_swiftshader_icd.json',
           'llvmpipe': '/usr/share/vulkan/icd.d/lvp_icd.json'}
D, F, NH, CAP, LAYERS, VOCAB, CHUNK = 768, 3072, 12, 1024, 12, 50257, 12565
LAYER_NAMES = ['g1', 'b1', 'wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo', 'g2', 'b2',
               'wfc', 'bfc', 'wproj', 'bproj']


def array_bytes(x):
    """The bytes of a Wasm array of binary32 values: the length, then each value's bits, as
    little-endian 64-bit words."""
    bits = np.ascontiguousarray(x, dtype=np.float32).reshape(-1).view(np.uint32).astype('<u8')
    return np.concatenate([np.array([bits.size], dtype='<u8'), bits]).tobytes()


def export(model):
    stamp = OUT / 'revision'
    if stamp.exists() and stamp.read_text() == REVISION:
        return
    OUT.mkdir(parents=True, exist_ok=True)
    tr = model.transformer

    def write(name, tensor):
        (OUT / f'{name}.bin').write_bytes(array_bytes(tensor.detach().float().numpy()))

    wte = tr.wte.weight
    for c in range(4):
        write(f'wte{c}', wte[c * CHUNK:(c + 1) * CHUNK])
    write('wpe', tr.wpe.weight)
    for l, layer in enumerate(tr.h):
        w = layer.attn.c_attn.weight
        b = layer.attn.c_attn.bias
        parts = [layer.ln_1.weight, layer.ln_1.bias,
                 w[:, :D], b[:D], w[:, D:2 * D], b[D:2 * D], w[:, 2 * D:], b[2 * D:],
                 layer.attn.c_proj.weight, layer.attn.c_proj.bias,
                 layer.ln_2.weight, layer.ln_2.bias,
                 layer.mlp.c_fc.weight, layer.mlp.c_fc.bias,
                 layer.mlp.c_proj.weight, layer.mlp.c_proj.bias]
        for name, tensor in zip(LAYER_NAMES, parts):
            write(f'l{l}_{name}', tensor)
    write('gf', tr.ln_f.weight)
    write('bf', tr.ln_f.bias)
    stamp.write_text(REVISION)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--driver', choices=DRIVERS, default='llvmpipe')
    parser.add_argument('--tokens', type=int, default=32)
    parser.add_argument('--save', help='writes the scores of each step to this .npy file')
    parser.add_argument('--export', action='store_true',
                        help='writes the weight files to build/gpt2-32 and stops')
    parser.add_argument('prompt', nargs='?', default='The meaning of life is')
    args = parser.parse_args()
    tokenizer = GPT2TokenizerFast.from_pretrained(REPO, revision=REVISION)
    model = GPT2LMHeadModel.from_pretrained(REPO, revision=REVISION, dtype=torch.float32).eval()
    export(model)
    if args.export:
        return
    prompt = tokenizer(args.prompt)['input_ids']
    if len(prompt) + args.tokens > CAP:
        sys.exit(f'prompt and completion exceed {CAP} tokens')
    scores_path = OUT / f'scores-{args.driver}.bin'
    env = dict(os.environ, VK_ICD_FILENAMES=DRIVERS[args.driver])
    start = time.time()
    run = subprocess.run(
        [str(ROOT / 'tools/leanrun'), '--timeout', '6h', 'lake', 'env', 'lean', '--run',
         'Examples/Gpt32/Generate.lean', str(HOST), str(OUT), str(WGSL), str(scores_path),
         str(NH), str(F), str(CHUNK), str(VOCAB), str(LAYERS), str(args.tokens)] +
        [str(i) for i in prompt],
        cwd=ROOT, env=env, check=True, stdout=subprocess.PIPE, text=True)
    elapsed = time.time() - start
    ids = [int(t) for t in run.stdout.strip().split('\n')[-1].split()]
    saved = np.fromfile(scores_path, dtype='<f4').reshape(-1, VOCAB)
    worst = 0.0
    differ = 0
    for k, scores in enumerate(saved):
        p = len(prompt) - 1 + k
        with torch.no_grad():
            reference = model(torch.tensor([ids[:p + 1]])).logits[0, -1].numpy()
        rel = float(np.max(np.abs(scores - reference)) / np.max(np.abs(reference)))
        worst = max(worst, rel)
        token = ids[p + 1]
        hf_token = int(np.argmax(reference))
        if token != hf_token:
            differ += 1
            gap = float(reference[hf_token] - reference[token])
            print(f'step {p}: ours {token}, Hugging Face {hf_token}, gap {gap:.3g}')
    if args.save:
        np.save(args.save, saved)
    print(tokenizer.decode(ids))
    print(f'{len(ids)} tokens, {elapsed:.1f} s for {len(ids) - 1} steps on {args.driver}, '
          f'with the start of Lean and the host; '
          f'largest relative score difference {worst:.3g}; {differ} choices differ from '
          f'Hugging Face')


if __name__ == '__main__':
    main()
