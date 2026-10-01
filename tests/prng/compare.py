# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Compares prng.wasm with SplitMix64 as Sebastiano Vigna's reference C code computes it
(https://prng.di.unimi.it/splitmix64.c), written here with Python integers reduced
modulo 2 ** 64.

Run with `uv run tests/prng/compare.py [path/to/prng.wasm]`.  The script checks the
first output for seed 0 against the published value 0xe220a8397b1dcdaf, one step from
106 seeds, including 0, 2 ** 64 - 1, and seeds whose advance wraps, and 1,000
successive steps from seeds 0 and 42 in one host session.  It checks the bits of
`unitFloat` against `(x >> 11) / 2 ** 53` for 40 words.  It fails on the first
difference."""
import pathlib
import random
import struct
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
HOST = ROOT / 'build/tools/leanexe-wasmtime-host'
WASM = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'build/prng/prng.wasm'
MASK = 2 ** 64 - 1
GAMMA = 0x9e3779b97f4a7c15


def reference(state):
    state = (state + GAMMA) & MASK
    z = state
    z = ((z ^ (z >> 30)) * 0xbf58476d1ce4e5b9) & MASK
    z = ((z ^ (z >> 27)) * 0x94d049bb133111eb) & MASK
    return state, z ^ (z >> 31)


def session(lines):
    out = subprocess.run([str(HOST), 'session', str(WASM)], input='\n'.join(lines) + '\n',
                         capture_output=True, text=True, check=True).stdout
    return [tuple(int(w) for w in line.split()[1:]) for line in out.splitlines()]


def fail(message):
    raise SystemExit(f'fail: {message}')


def main():
    if reference(0)[1] != 0xe220a8397b1dcdaf:
        fail('the reference does not give the published first output for seed 0')
    rng = random.Random(1)
    seeds = [0, 1, 2 ** 63, MASK, GAMMA, 2 ** 64 - GAMMA] + [rng.getrandbits(64) for _ in range(100)]
    got = session([line for s in seeds for line in (f'arg-u64 {s}', 'call splitMix 2')])
    for s, g in zip(seeds, got):
        if g != reference(s):
            fail(f'splitMix {s}: {g}, expected {reference(s)}')
    steps = 0
    for seed in (0, 42):
        lines = []
        state = seed
        expected = []
        for _ in range(1000):
            lines += [f'arg-u64 {state}', 'call splitMix 2']
            state, word = reference(state)
            expected.append((state, word))
        got = session(lines)
        if got != expected:
            index = next(i for i, (g, e) in enumerate(zip(got, expected)) if g != e)
            fail(f'step {index} from seed {seed}: {got[index]}, expected {expected[index]}')
        steps += len(got)
    words = [0, 1, 2 ** 11 - 1, 2 ** 11, 2 ** 63, MASK] + [rng.getrandbits(64) for _ in range(34)]
    for x in words:
        out = subprocess.run([str(HOST), 'call', str(WASM), 'unitFloat', 'f64', f'i64:{x}'],
                             capture_output=True, text=True, check=True).stdout.strip()
        expected = struct.unpack('<Q', struct.pack('<d', (x >> 11) / 2 ** 53))[0]
        if int(out) != expected:
            fail(f'unitFloat {x}: {out}, expected {expected}')
    print(f'splitMix matched on {len(seeds)} seeds and {steps} successive steps; '
          f'unitFloat matched on {len(words)} words')


main()
