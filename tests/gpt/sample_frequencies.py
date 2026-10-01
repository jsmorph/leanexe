# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks that gpt.wasm's `sampleTopK` draws tokens with the probabilities of top-k
sampling.

Run with `uv run tests/gpt/sample_frequencies.py [path/to/gpt.wasm]`.  For several score
arrays, values of k, and temperatures, the script calls `sampleTopK` 20,000 times in one
host session, passing the generator state from each call to the next, and compares the
count of each token with the expected count: zero for tokens below the k-th largest score,
counted with repeats, and otherwise `exp ((score - max) / temperature)` over the total of
the kept tokens.  It fails if a token outside the kept set is drawn or if a count differs
from its expectation by more than five standard deviations."""
import math
import pathlib
import struct
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
HOST = ROOT / 'build/tools/leanexe-wasmtime-host'
WASM = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'build/gpt/gpt.wasm'
DRAWS = 20000


def bits(x):
    return struct.unpack('<Q', struct.pack('<d', x))[0]


def expected(scores, k, temperature):
    threshold = sorted(scores, reverse=True)[min(k, len(scores)) - 1]
    top = max(scores)
    weights = [math.exp((s - top) / temperature) if s >= threshold else 0.0 for s in scores]
    total = sum(weights)
    return [w / total for w in weights]


def draws(scores, k, temperature, seed):
    """The count of each token over `DRAWS` calls of `sampleTopK`, starting from state
    `seed`."""
    counts = [0] * len(scores)
    state = seed
    proc = subprocess.Popen([str(HOST), 'session', str(WASM)], stdin=subprocess.PIPE,
                            stdout=subprocess.PIPE, text=True)
    proc.stdin.write(f'alloc 1 {8 * (len(scores) + 1)}\nwrite-u64 1 0 {len(scores)}\n')
    for i, s in enumerate(scores):
        proc.stdin.write(f'write-u64 1 {8 * (i + 1)} {bits(s)}\n')
    for _ in range(DRAWS):
        proc.stdin.write(f'arg-ptr 1\narg-u64 {k}\narg-f64 {bits(temperature)}\n'
                         f'arg-u64 {state}\ncall sampleTopK 2\n')
        proc.stdin.flush()
        words = proc.stdout.readline().split()
        if words[:1] != ['results']:
            raise SystemExit(f'fail: unexpected reply {words}')
        token, state = int(words[1]), int(words[2])
        counts[token] += 1
    proc.stdin.close()
    proc.wait()
    return counts


def main():
    cases = [([1.0, 2.0, 3.0, 0.5, -1.0], 3, 1.0), ([1.0, 2.0, 3.0, 0.5, -1.0], 5, 0.7),
             ([2.0, 2.0, 1.0, 2.0, 0.0], 2, 1.0), ([0.0, 0.1, 0.2, 0.3, 0.4, 0.5], 4, 0.25),
             ([5.0, 1.0, 1.0, 1.0], 1, 1.0), ([3.0, 2.9, 2.8, -5.0], 3, 2.0)]
    for n, (scores, k, temperature) in enumerate(cases):
        p = expected(scores, k, temperature)
        counts = draws(scores, k, temperature, 1000 + n)
        worst = 0.0
        for token, (c, q) in enumerate(zip(counts, p)):
            if q == 0.0:
                if c:
                    raise SystemExit(f'fail: case {n}: token {token} outside the top {k} drawn {c} times')
                continue
            sd = math.sqrt(DRAWS * q * (1 - q)) or 1.0
            worst = max(worst, abs(c - DRAWS * q) / sd)
        if worst > 5.0:
            raise SystemExit(f'fail: case {n}: counts {counts}, expected {[DRAWS * q for q in p]}')
        print(f'case {n}: k={k} temperature={temperature} counts {counts}, '
              f'largest deviation {worst:.2f} standard deviations')


main()
