#!/usr/bin/env -S uv run --script
# /// script
# requires-python = ">=3.12"
# dependencies = ["transformers==5.18.0"]
# ///
"""Generates text with GPT-2 124M on gpt.wasm.

Usage: `uv run tools/gpt2.py --output-tokens 32 --prompt "It was a dark and stormy night"`,
with `--top-k 40` to sample, and `--temperature` and `--seed` to control the sampling.

The program tokenizes the prompt with the pinned `openai-community/gpt2` tokenizer, runs
the compiled `step` on each prompt token in one host session that keeps the weights
loaded, and then repeatedly chooses a token from the scores of `scores` and runs `step`
on it.  Without `--top-k` it takes the token with the highest score.  With `--top-k K` it
calls the compiled `sampleTopK`, which draws from the tokens whose scores are at least the
K-th largest, with weights `exp ((score - max) / temperature)` and a SplitMix64 state that
the program passes from one token to the next.  Without `--seed` the state starts from 8
bytes of `os.urandom`, and the program prints the seed to stderr so that a run can be
repeated.  It prints the prompt and each token as it is chosen, and it stops after the
requested number of tokens or when it chooses `<|endoftext|>`, which it does not print.
The weights
are the binary64 files that `tests/gpt/gpt2_compare.py` writes to build/gpt2-124m/."""
import argparse
import array
import os
import pathlib
import struct
import subprocess
import sys
import tempfile

os.environ.setdefault('TRANSFORMERS_VERBOSITY', 'error')
from transformers import GPT2Config, GPT2TokenizerFast  # noqa: E402

ROOT = pathlib.Path(__file__).resolve().parents[1]
HOST = ROOT / 'build/tools/leanexe-wasmtime-host'
WASM = ROOT / 'build/gpt/gpt.wasm'
WEIGHTS = ROOT / 'build/gpt2-124m'
REPO = 'openai-community/gpt2'
REVISION = '607a30d783dfa663caf39e06633721c8d4cfcd7e'
NAMES = ['wte', 'wpe', 'g1', 'b1', 'wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo', 'g2', 'b2',
         'wfc', 'bfc', 'wproj', 'bproj', 'gf', 'bf']


class Session:
    """A host session on gpt.wasm with the weights in allocations 1 to 20 and the empty
    cache in allocation 30."""

    def __init__(self, config, scores_path):
        self.config = config
        self.scores_path = scores_path
        self.eps = struct.unpack('<Q', struct.pack('<d', config.layer_norm_epsilon))[0]
        self.proc = subprocess.Popen([str(HOST), 'session', str(WASM)], stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, text=True)
        for i, name in enumerate(NAMES):
            self.send(f'file-u64 {i + 1} {WEIGHTS / (name + ".u64")}')
        self.send('alloc 30 8')
        self.send('write-u64 30 0 0')

    def send(self, line):
        self.proc.stdin.write(line + '\n')
        self.proc.stdin.flush()

    def reply(self, prefix):
        words = self.proc.stdout.readline().split()
        if words[:1] != [prefix]:
            raise SystemExit(f'gpt2: unexpected reply from the host: {words}')
        return words

    def call(self, name, args):
        for a in args:
            self.send(a)
        self.send(f'call {name} 1')
        return int(self.reply('results')[1])

    @staticmethod
    def arg(ptr):
        return 'arg-ptr 30' if ptr is None else f'arg-u64 {ptr}'

    def release(self, ptr):
        self.send(self.arg(ptr))
        self.send('call release 0')
        self.reply('results')

    def step(self, cache, token):
        c = self.config
        args = [self.arg(cache)] + [f'arg-ptr {i}' for i in range(1, 19)]
        args += [f'arg-u64 {token}', f'arg-u64 {c.n_layer}', f'arg-u64 {c.n_head}',
                 f'arg-u64 {c.n_embd // c.n_head}', f'arg-u64 {c.n_inner or 4 * c.n_embd}',
                 f'arg-f64 {self.eps}']
        return self.call('step', args)

    def scores(self, cache):
        c = self.config
        return self.call('scores', [self.arg(cache), 'arg-ptr 1', 'arg-ptr 19', 'arg-ptr 20',
                                    f'arg-u64 {c.n_layer}', f'arg-u64 {c.n_head}',
                                    f'arg-u64 {c.n_embd // c.n_head}', f'arg-u64 {c.vocab_size}',
                                    f'arg-f64 {self.eps}'])

    def sample(self, cache, k, temperature, state):
        """A token drawn by `sampleTopK` from the scores after the last position of `cache`,
        and the next generator state."""
        ptr = self.scores(cache)
        bits = struct.unpack('<Q', struct.pack('<d', temperature))[0]
        for a in [f'arg-u64 {ptr}', f'arg-u64 {k}', f'arg-f64 {bits}', f'arg-u64 {state}']:
            self.send(a)
        self.send('call sampleTopK 2')
        token, state = (int(w) for w in self.reply('results')[1:3])
        self.release(ptr)
        return token, state

    def next_token(self, cache):
        """The token with the highest score after the last position of `cache`."""
        ptr = self.scores(cache)
        self.send(f'save-u64 {ptr} {self.scores_path}')
        self.reply('saved')
        self.release(ptr)
        scores = array.array('d')
        scores.frombytes(self.scores_path.read_bytes())
        if sys.byteorder != 'little':
            scores.byteswap()
        return max(range(len(scores)), key=scores.__getitem__)

    def close(self):
        self.proc.stdin.close()
        self.proc.wait()


def main():
    parser = argparse.ArgumentParser(description='Generate text with GPT-2 124M on gpt.wasm.')
    parser.add_argument('--prompt', required=True, help='the text to continue')
    parser.add_argument('--output-tokens', type=int, default=32,
                        help='the largest number of tokens to generate (default 32); '
                        'generation also stops at <|endoftext|>')
    parser.add_argument('--top-k', type=int,
                        help='sample from the K highest-scoring tokens (1 to 1024); '
                        'without it, take the highest-scoring token')
    parser.add_argument('--temperature', type=float, default=1.0,
                        help='divide the score differences by T before sampling (default 1.0)')
    parser.add_argument('--seed', type=int,
                        help='the starting SplitMix64 state, 0 to 2^64 - 1 '
                        '(default: random, printed to stderr)')
    args = parser.parse_args()
    if args.top_k is not None and not 1 <= args.top_k <= 1024:
        raise SystemExit('gpt2: --top-k must be from 1 to 1024')
    if not (args.temperature > 0 and args.temperature < float('inf')):
        raise SystemExit('gpt2: --temperature must be positive and finite')
    if args.seed is not None and not 0 <= args.seed < 2 ** 64:
        raise SystemExit('gpt2: --seed must be from 0 to 2^64 - 1')
    state = args.seed
    if args.top_k is not None and state is None:
        state = int.from_bytes(os.urandom(8), 'little')
        print(f'seed {state}', file=sys.stderr)
    for path, how in [(HOST, 'tools/build-wasmtime-host.sh'),
                      (WASM, 'the Emit.lean command for Examples.Gpt.Module in docs/design.md'),
                      (WEIGHTS / 'revision', 'uv run tests/gpt/gpt2_compare.py')]:
        if not path.exists():
            raise SystemExit(f'gpt2: missing {path.relative_to(ROOT)}; create it with {how}')
    if (WEIGHTS / 'revision').read_text() != REVISION:
        raise SystemExit('gpt2: build/gpt2-124m holds another revision; '
                         'rerun uv run tests/gpt/gpt2_compare.py')
    tokenizer = GPT2TokenizerFast.from_pretrained(REPO, revision=REVISION)
    config = GPT2Config.from_pretrained(REPO, revision=REVISION)
    ids = tokenizer(args.prompt)['input_ids']
    if not ids:
        raise SystemExit('gpt2: the prompt is empty')
    if args.output_tokens < 0 or len(ids) + args.output_tokens > config.n_positions:
        raise SystemExit(f'gpt2: the prompt and the output must fit in {config.n_positions} tokens')
    with tempfile.TemporaryDirectory() as tmp:
        session = Session(config, pathlib.Path(tmp) / 'scores.u64')
        cache = None
        for token in ids:
            cache = session.step(cache, token)
        text = tokenizer.decode(ids)
        print(text, end='', flush=True)
        for n in range(args.output_tokens):
            if args.top_k is None:
                token = session.next_token(cache)
            else:
                token, state = session.sample(cache, args.top_k, args.temperature, state)
            if token == config.eos_token_id:
                break
            ids.append(token)
            full = tokenizer.decode(ids)
            print(full[len(text):], end='', flush=True)
            text = full
            if n + 1 < args.output_tokens:
                cache = session.step(cache, token)
        session.release(cache)
        session.close()
    print()


main()
