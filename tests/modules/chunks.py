# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Runs a stream of CLOB commands through `clob.wasm` three ways in host sessions: one call of
`runCommands` over the whole stream, calls over chunks that pass the book back in, and one call
of `applyCommand` per command.  Checks that the three books agree.  Does the same for `runOut`
and `stepCommand`, which also append the best bid after each command to an output array, and
checks that `runOut` leaves the book of `runCommands`.  Whether an insert or an append grows
its array depends on the capacity the allocator gave its block, which differs between
sessions, so the counts are checked to leave exactly the results and the command arrays
allocated.

Usage: uv run tests/modules/chunks.py [build directory]"""

import random
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BUILD = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'build'
HOST = ROOT / 'build' / 'tools' / 'leanexe-wasmtime-host'
WASM = BUILD / 'clob' / 'clob.wasm'


def write_words(path, words):
    path.write_bytes(struct.pack(f'<{len(words)}Q', *words))


def read_words(path):
    data = path.read_bytes()
    return list(struct.unpack(f'<{len(data) // 8}Q', data))


def session(script):
    out = subprocess.run([HOST, 'session', WASM], input=script, capture_output=True, text=True,
                         check=True).stdout
    stats = [line for line in out.splitlines() if line.startswith('stats')][-1].split()
    return int(stats[1]), int(stats[2])


def book_and_commands(rng, levels, count):
    prices = sorted(rng.sample(range(50, 200), levels), reverse=True)
    sizes = [rng.randrange(1, 20) for _ in prices]
    commands = []
    for _ in range(count):
        near = rng.choice(prices) if prices and rng.random() < 0.7 else rng.randrange(40, 210)
        commands += [rng.randrange(3), near, rng.randrange(1, 25)]
    return prices, sizes, commands


def run(directory, arrays, commands, cuts):
    """The arrays after the commands, passed in chunks that end at the word offsets `cuts`, and
    the session's allocation and free counts.  `arrays` is the book, for `runCommands`, or the
    book and an output array, for `runOut`."""
    d = Path(directory)
    n = len(arrays)
    name = 'runCommands' if n == 2 else 'runOut'
    script = ''
    for k, words in enumerate(arrays):
        write_words(d / f'in{k}', words)
        script += f'file-u64 {10 + k} {d / f"in{k}"}\n'
    state = [10 + k for k in range(n)]
    bounds = [0] + cuts + [len(commands)]
    for c, (a, b) in enumerate(zip(bounds, bounds[1:])):
        write_words(d / f'chunk{c}', commands[a:b])
        script += f'file-u64 {100 + c} {d / f"chunk{c}"}\n'
        script += ''.join(f'arg-ptr {s}\n' for s in state)
        script += f'arg-ptr {100 + c}\ncall {name} {n}\n'
        state = [1000 + n * c + k for k in range(n)]
        script += ''.join(f'keep {s} result:{k}\n' for k, s in enumerate(state))
    script += ''.join(f'save-u64 result:{k} {d / f"out{k}"}\n' for k in range(n)) + 'stats\n'
    counts = session(script)
    return [read_words(d / f'out{k}') for k in range(n)], counts


def run_steps(directory, arrays, commands):
    """The arrays after one `applyCommand` call per command, or one `stepCommand` call when
    `arrays` holds an output array, and the session's counts."""
    d = Path(directory)
    n = len(arrays)
    name = 'applyCommand' if n == 2 else 'stepCommand'
    script = ''
    for k, words in enumerate(arrays):
        write_words(d / f'in{k}', words)
        script += f'file-u64 {10 + k} {d / f"in{k}"}\n'
    state = [10 + k for k in range(n)]
    for c in range(len(commands) // 3):
        kind, price, size = commands[3 * c:3 * c + 3]
        script += ''.join(f'arg-ptr {s}\n' for s in state)
        script += f'arg-u64 {kind}\narg-u64 {price}\narg-u64 {size}\ncall {name} {n}\n'
        state = [1000 + n * c + k for k in range(n)]
        script += ''.join(f'keep {s} result:{k}\n' for k, s in enumerate(state))
    script += ''.join(f'save-u64 result:{k} {d / f"out{k}"}\n' for k in range(n)) + 'stats\n'
    counts = session(script)
    return [read_words(d / f'out{k}') for k in range(n)], counts


def main():
    rng = random.Random(7)
    failed = 0
    cases = 0
    for trial in range(40):
        prices, sizes, commands = book_and_commands(rng, rng.randrange(0, 9), rng.randrange(1, 60))
        whole = len(commands) // 3
        splits = [[], [3 * k for k in range(1, whole)],
                  sorted(3 * k for k in rng.sample(range(1, whole), min(3, whole - 1)))]
        out = [rng.randrange(2 ** 64) for _ in range(rng.randrange(0, 4))]
        with tempfile.TemporaryDirectory() as directory:
            for arrays in ([prices, sizes], [prices, sizes, out]):
                one, (allocs, frees) = run(directory, arrays, commands, [])
                steps, step_counts = run_steps(directory, arrays, commands)
                for cuts in splits:
                    cases += 1
                    chunked, (c_allocs, c_frees) = run(directory, arrays, commands, cuts)
                    # The results and one commands array per chunk stay allocated.
                    counted = c_allocs - c_frees == len(arrays) + len(cuts) + 1
                    if chunked != one or not counted:
                        failed += 1
                        print(f'fail: trial {trial}, {len(arrays)} arrays, cuts {cuts}: {chunked} '
                              f'with {c_allocs} allocations and {c_frees} frees, against {one} '
                              f'with {allocs} and {frees}')
                cases += 1
                # The steps leave the results allocated, and one call also its commands array.
                counted = (step_counts[0] - step_counts[1] == len(arrays) and
                           allocs - frees == len(arrays) + 1)
                if steps != one or not counted:
                    failed += 1
                    print(f'fail: trial {trial}, {len(arrays)} arrays, steps: {steps} with counts '
                          f'{step_counts}, against {one} with {(allocs, frees)}')
                if len(arrays) == 2:
                    book = one
                else:
                    cases += 1
                    if one[:2] != book or len(one[2]) != len(out) + 2 * whole:
                        failed += 1
                        print(f'fail: trial {trial}: runOut left {one}, expected the book {book} '
                              f'and {len(out) + 2 * whole} output words')
    print(f'chunks: {cases} cases, {failed} failed')
    sys.exit(1 if failed else 0)


main()
