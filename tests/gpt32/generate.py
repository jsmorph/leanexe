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
Project/Gpt32/Specs.lean, run by build/tools/leanexe-webgpu-host in session mode.

Run with `uv run tests/gpt32/generate.py [--driver swiftshader|llvmpipe] [--tokens N] [PROMPT]`.
The script writes the pinned openai-community/gpt2 checkpoint to build/gpt2-32/ as Wasm arrays
of binary32 values (8 bytes per value), one file per array: the token embedding in four chunks
of at most 12,565 rows, the positional embedding, and each layer's arrays, with `c_attn` split
into its `q`, `k`, and `v` columns.  It emits any missing kernel text with Project/WGSL/Emit.lean.
Each token runs the dispatches of one step in the order of `LeanExe.Examples.Gpt32`'s kernels,
reads the scores, and takes the largest.  For each step it also runs Hugging Face's float32 model
on the same prefix and reports the largest score difference relative to the largest score and
whether the two models choose the same token."""
import argparse
import os
import pathlib
import subprocess
import sys
import tempfile
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
KERNELS = {'exp': 'Project.Gpt32.Kernels'} | {
    name: 'Project.Gpt32.Specs' for name in
    ['embed', 'layerNorm', 'linear', 'append', 'scores', 'headMax', 'headSum', 'probs', 'mix',
     'add', 'gelu', 'logits']}
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


def emit():
    for name, module in KERNELS.items():
        path = WGSL / f'{name}.wgsl'
        if path.exists():
            continue
        WGSL.mkdir(parents=True, exist_ok=True)
        subprocess.run([str(ROOT / 'tools/leanrun'), '--timeout', '10m', 'lake', 'env', 'lean',
                        '--run', 'Project/WGSL/Emit.lean', module,
                        f'{module.rsplit(".", 1)[0]}.{name}Kernel', str(path)],
                       cwd=ROOT, check=True)


class Session:
    """A host session: one device, named buffers, and the kernels."""

    def __init__(self, driver):
        env = dict(os.environ, VK_ICD_FILENAMES=DRIVERS[driver])
        self.proc = subprocess.Popen([str(HOST), 'session'], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True, env=env)
        self.words = set()
        self.tmp = tempfile.TemporaryDirectory()

    def cmd(self, line):
        self.proc.stdin.write(line + '\n')
        self.proc.stdin.flush()
        reply = self.proc.stdout.readline().strip()
        if reply != 'ok':
            sys.exit(f'host failed on: {line}')

    def word(self, v):
        name = f'w{v}'
        if name not in self.words:
            self.cmd(f'words {name} u64:{v}')
            self.words.add(name)
        return name

    def float(self, x):
        bits = int(np.array([x], dtype=np.float32).view(np.uint32)[0])
        name = f'f{bits}'
        if name not in self.words:
            self.cmd(f'words {name} u32:{bits},0')
            self.words.add(name)
        return name

    def run(self, kernel, n, out, *inputs):
        self.cmd(f'output {out} {n}')
        self.cmd(f'run {kernel} {max(1, (n + 63) // 64)} {out} {" ".join(inputs)}')

    def read(self, name):
        path = pathlib.Path(self.tmp.name) / f'{name}.bin'
        self.cmd(f'read {name} {path}')
        words = np.frombuffer(path.read_bytes(), dtype='<u4')
        return words[2::2].view(np.float32).copy()

    def close(self):
        self.proc.stdin.write('quit\n')
        self.proc.stdin.close()
        if self.proc.wait() != 0:
            sys.exit('host failed on quit')


def load(s):
    for path in sorted(OUT.glob('*.bin')):
        s.cmd(f'load {path.stem} {path}')
    for name in KERNELS:
        s.cmd(f'shader {name} {WGSL / name}.wgsl')
    for l in range(LAYERS):
        s.cmd(f'words kc{l}_0 u64:0')
        s.cmd(f'words vc{l}_0 u64:0')


def step(s, token, p):
    """The scores after `token` at position `p`, with the caches of positions below `p`."""
    w = s.word
    c, row = divmod(token, CHUNK)
    s.run('embed', D, 'x', f'wte{c}', 'wpe', w(row), w(p), w(D))
    for l in range(LAYERS):
        L = lambda name: f'l{l}_{name}'
        s.run('layerNorm', D, 'h1', 'x', L('g1'), L('b1'), w(D), s.float(D))
        for part in 'qkv':
            s.run('linear', D, part, 'h1', L(f'w{part}'), L(f'b{part}'), w(D), w(D))
        s.run('append', (p + 1) * D, f'kc{l}_{p + 1}', f'kc{l}_{p}', 'k', w(p * D), w((p + 1) * D))
        s.run('append', (p + 1) * D, f'vc{l}_{p + 1}', f'vc{l}_{p}', 'v', w(p * D), w((p + 1) * D))
        s.cmd(f'free kc{l}_{p}')
        s.cmd(f'free vc{l}_{p}')
        s.run('scores', NH * CAP, 'sc', 'q', f'kc{l}_{p + 1}', w(p), w(D), w(NH * CAP))
        s.run('headMax', NH, 'mx', 'sc', w(p), w(NH))
        s.run('headSum', NH, 'sm', 'sc', 'mx', w(p), w(NH))
        s.run('probs', NH * CAP, 'pw', 'sc', 'mx', 'sm', w(p), w(NH * CAP))
        s.run('mix', D, 'o', 'pw', f'vc{l}_{p + 1}', w(p), w(D))
        s.run('linear', D, 'a', 'o', L('wo'), L('bo'), w(D), w(D))
        s.run('add', D, 'r', 'x', 'a')
        s.run('layerNorm', D, 'h2', 'r', L('g2'), L('b2'), w(D), s.float(D))
        s.run('linear', F, 'm1', 'h2', L('wfc'), L('bfc'), w(D), w(F))
        s.run('gelu', F, 'g', 'm1')
        s.run('linear', D, 'm2', 'g', L('wproj'), L('bproj'), w(F), w(D))
        s.run('add', D, 'x', 'r', 'm2')
    s.run('layerNorm', D, 'hf', 'x', 'gf', 'bf', w(D), s.float(D))
    scores = []
    for c in range(4):
        rows = min(CHUNK, VOCAB - c * CHUNK)
        s.run('logits', rows, f'z{c}', 'hf', f'wte{c}', w(rows), w(D))
        scores.append(s.read(f'z{c}'))
    return np.concatenate(scores)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--driver', choices=DRIVERS, default='llvmpipe')
    parser.add_argument('--tokens', type=int, default=32)
    parser.add_argument('prompt', nargs='?', default='The meaning of life is')
    args = parser.parse_args()
    tokenizer = GPT2TokenizerFast.from_pretrained(REPO, revision=REVISION)
    model = GPT2LMHeadModel.from_pretrained(REPO, revision=REVISION, dtype=torch.float32).eval()
    export(model)
    emit()
    ids = tokenizer(args.prompt)['input_ids']
    if len(ids) + args.tokens > CAP:
        sys.exit(f'prompt and completion exceed {CAP} tokens')
    s = Session(args.driver)
    start = time.time()
    load(s)
    print(f'loaded in {time.time() - start:.1f} s', flush=True)
    worst = 0.0
    differ = 0
    start = time.time()
    for p in range(len(ids) + args.tokens - 1):
        scores = step(s, ids[p], p)
        if p + 1 < len(ids):
            continue
        with torch.no_grad():
            reference = model(torch.tensor([ids[:p + 1]])).logits[0, -1].numpy()
        rel = float(np.max(np.abs(scores - reference)) / np.max(np.abs(reference)))
        worst = max(worst, rel)
        token = int(np.argmax(scores))
        hf_token = int(np.argmax(reference))
        if token != hf_token:
            differ += 1
            gap = float(reference[hf_token] - reference[token])
            print(f'step {p}: ours {token}, Hugging Face {hf_token}, gap {gap:.3g}')
        ids.append(token)
    elapsed = time.time() - start
    s.close()
    print(tokenizer.decode(ids))
    print(f'{len(ids)} tokens, {elapsed:.1f} s for {len(ids) - 1} steps on {args.driver}; '
          f'largest relative score difference {worst:.3g}; {differ} choices differ from '
          f'Hugging Face')


if __name__ == '__main__':
    main()
