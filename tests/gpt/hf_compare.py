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
"""Compares gpt.wasm's `forward` with Hugging Face's GPT2LMHeadModel in float64.

Run with `uv run tests/gpt/hf_compare.py [path/to/gpt.wasm]`.  The model uses the
explicit ("eager") attention, no dropout, and every parameter drawn from a normal
distribution with standard deviation 0.5, with 1 added to the layer-norm gains.  The
same arrays and token ids go to `forward`, with `c_attn` split into its `q`, `k`, and
`v` columns and each of the sixteen layer arrays stacked layer after layer.  The host
takes arrays on its command line, which limits each array to about 6,000 values.  The
script fails if any score differs from Hugging Face's by more than
1e-12 of the largest score."""
import pathlib
import struct
import subprocess
import sys

import torch
from transformers import GPT2Config, GPT2LMHeadModel

ROOT = pathlib.Path(__file__).resolve().parents[2]
HOST = ROOT / 'build/tools/leanexe-wasmtime-host'
WASM = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'build/gpt/gpt.wasm'
EPS = 1e-5
LIMIT = 1e-12


def bits(values):
    return ','.join(str(struct.unpack('<Q', struct.pack('<d', float(v)))[0]) for v in values)


def from_bits(text):
    return [struct.unpack('<d', struct.pack('<Q', int(v)))[0] for v in text.split(',') if v]


def flat(tensor):
    return tensor.detach().contiguous().reshape(-1).tolist()


def compare(nh, dh, f, vocab, t, layers, seed):
    """Returns the number of scores, the largest score, and the largest difference."""
    d = nh * dh
    torch.manual_seed(seed)
    config = GPT2Config(vocab_size=vocab, n_positions=t, n_embd=d, n_layer=layers, n_head=nh,
                        n_inner=f, activation_function='gelu_new', resid_pdrop=0.0,
                        embd_pdrop=0.0, attn_pdrop=0.0, layer_norm_epsilon=EPS,
                        bos_token_id=None, eos_token_id=None)
    model = GPT2LMHeadModel._from_config(config, attn_implementation='eager').double().eval()
    assert model.config._attn_implementation == 'eager'
    with torch.no_grad():
        for name, p in model.named_parameters():
            p.normal_(0.0, 0.5)
            if '.ln_' in name and name.endswith('weight'):
                p.add_(1.0)
        tokens = torch.randint(0, vocab, (1, t))
        scores = flat(model(tokens).logits[0])
    tr = model.transformer
    args = [f'array-u64:{",".join(str(int(x)) for x in tokens[0].tolist())}',
            f'array-u64:{bits(flat(tr.wte.weight))}', f'array-u64:{bits(flat(tr.wpe.weight[:t]))}']
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
    args += [f'array-u64:{bits(values)}' for values in stacked]
    args += [f'array-u64:{bits(flat(tr.ln_f.weight))}', f'array-u64:{bits(flat(tr.ln_f.bias))}',
             f'i64:{layers}', f'i64:{t}', f'i64:{nh}', f'i64:{dh}', f'i64:{f}', f'i64:{vocab}', f'f64:{bits([EPS])}']
    out = subprocess.run([str(HOST), 'call', str(WASM), 'forward', 'array-u64'] + args,
                         capture_output=True, text=True, check=True).stdout
    ours = from_bits(out.strip().strip('[]').replace(' ', ''))
    if len(ours) != len(scores):
        raise SystemExit(f'forward returned {len(ours)} scores, Hugging Face {len(scores)}')
    return len(scores), max(abs(x) for x in scores), max(abs(a - b) for a, b in zip(ours, scores))


def main():
    configs = [(1, 4, 16, 10, 5, 1), (2, 4, 32, 20, 6, 2), (3, 2, 24, 17, 7, 3),
               (4, 4, 64, 50, 8, 2), (2, 8, 64, 30, 4, 1), (1, 1, 4, 5, 3, 12),
               (2, 3, 12, 11, 1, 6), (4, 2, 16, 13, 8, 12), (2, 4, 32, 20, 6, 12),
               (2, 2, 8, 7, 4, 0)]
    worst = 0.0
    for nh, dh, f, vocab, t, layers in configs:
        for seed in range(3):
            n, largest, diff = compare(nh, dh, f, vocab, t, layers, seed)
            worst = max(worst, diff / largest)
            print(f'nh={nh} dh={dh} f={f} vocab={vocab} t={t} layers={layers} seed={seed}: {n} scores, '
                  f'largest {largest:.3g}, largest difference {diff:.3g}')
    print(f'largest relative difference {worst:.3g}')
    if worst > LIMIT:
        raise SystemExit(f'difference above {LIMIT}')


main()
