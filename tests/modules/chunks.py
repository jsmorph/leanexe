# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///
"""Runs a stream of CLOB commands through `clob.wasm` three ways in host sessions: one call of
`runCommands` over the whole stream, calls over chunks that pass the book back in, and one call
of `applyCommand` per command.  Checks that the three books agree and that `runCommands`
allocates and frees exactly what the commands do, plus its own arguments.

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


def run(directory, prices, sizes, commands, cuts):
    """The book after the commands, passed in chunks that end at the word offsets `cuts`, and the
    session's allocation and free counts."""
    d = Path(directory)
    write_words(d / 'prices', prices)
    write_words(d / 'sizes', sizes)
    bounds = [0] + cuts + [len(commands)]
    script = f'file-u64 10 {d / "prices"}\nfile-u64 11 {d / "sizes"}\n'
    book = (10, 11)
    for n, (a, b) in enumerate(zip(bounds, bounds[1:])):
        write_words(d / f'chunk{n}', commands[a:b])
        script += f'file-u64 {100 + n} {d / f"chunk{n}"}\n'
        script += f'arg-ptr {book[0]}\narg-ptr {book[1]}\narg-ptr {100 + n}\ncall runCommands 2\n'
        script += f'keep {20 + 2 * n} result:0\nkeep {21 + 2 * n} result:1\n'
        book = (20 + 2 * n, 21 + 2 * n)
    script += f'save-u64 result:0 {d / "out-prices"}\nsave-u64 result:1 {d / "out-sizes"}\nstats\n'
    counts = session(script)
    return (read_words(d / 'out-prices'), read_words(d / 'out-sizes')), counts


def run_steps(directory, prices, sizes, commands):
    """The book after one `applyCommand` call per command, and the session's counts."""
    d = Path(directory)
    write_words(d / 'prices', prices)
    write_words(d / 'sizes', sizes)
    script = f'file-u64 10 {d / "prices"}\nfile-u64 11 {d / "sizes"}\n'
    book = (10, 11)
    for n in range(len(commands) // 3):
        kind, price, size = commands[3 * n:3 * n + 3]
        script += (f'arg-ptr {book[0]}\narg-ptr {book[1]}\narg-u64 {kind}\narg-u64 {price}\n'
                   f'arg-u64 {size}\ncall applyCommand 2\n'
                   f'keep {20 + 2 * n} result:0\nkeep {21 + 2 * n} result:1\n')
        book = (20 + 2 * n, 21 + 2 * n)
    script += f'save-u64 result:0 {d / "out-prices"}\nsave-u64 result:1 {d / "out-sizes"}\nstats\n'
    counts = session(script)
    return (read_words(d / 'out-prices'), read_words(d / 'out-sizes')), counts


def main():
    rng = random.Random(7)
    failed = 0
    cases = 0
    for trial in range(40):
        prices, sizes, commands = book_and_commands(rng, rng.randrange(0, 9), rng.randrange(1, 60))
        whole = len(commands) // 3
        splits = [[], [3 * k for k in range(1, whole)],
                  sorted(3 * k for k in rng.sample(range(1, whole), min(3, whole - 1)))]
        with tempfile.TemporaryDirectory() as directory:
            one, (allocs, frees) = run(directory, prices, sizes, commands, [])
            steps, step_counts = run_steps(directory, prices, sizes, commands)
            for cuts in splits:
                cases += 1
                chunked, (c_allocs, c_frees) = run(directory, prices, sizes, commands, cuts)
                # Each chunk adds its commands array; the frees are those of the commands.
                if chunked != one or c_allocs != allocs + len(cuts) or c_frees != frees:
                    failed += 1
                    print(f'fail: trial {trial}, cuts {cuts}: {chunked} with {c_allocs} '
                          f'allocations and {c_frees} frees, expected {one} with '
                          f'{allocs + len(cuts)} and {frees}')
            cases += 1
            # One `runCommands` call allocates its commands array beyond what the steps do.
            if steps != one or step_counts != (allocs - 1, frees):
                failed += 1
                print(f'fail: trial {trial}, steps: {steps} with counts {step_counts}, '
                      f'expected {one} with {(allocs - 1, frees)}')
    print(f'chunks: {cases} cases, {failed} failed')
    sys.exit(1 if failed else 0)


main()
