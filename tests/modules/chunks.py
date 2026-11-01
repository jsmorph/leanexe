# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Runs a stream of level commands through `insert.wasm` three ways in host sessions: one call
of `runLevels` over the whole stream, calls over chunks that pass the book side back in, and one
call of `applyLevel` per command.  Checks that the three sides agree.  Whether an insertion grows
its array depends on the capacity the allocator gave its block, which differs between sessions,
so the counts are checked to leave exactly the results and the command arrays allocated.

Usage: uv run tests/modules/chunks.py [path/to/insert.wasm].  Without a path the module is the
verified compiler's build/verified/insert.wasm, which tests/verified/run.sh writes."""

import random
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HOST = ROOT / 'build' / 'tools' / 'leanexe-wasmtime-host'
WASM = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / 'build' / 'verified' / 'insert.wasm'


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


def side_and_commands(rng, levels, count):
    """A side of `levels` levels and `count` commands of four words: the kind, which inserts,
    removes, or leaves the side, a position inside, at, or past the end of the side, a price, and
    a size."""
    prices = sorted(rng.sample(range(50, 200), levels), reverse=True)
    sizes = [rng.randrange(1, 20) for _ in prices]
    commands = []
    for _ in range(count):
        commands += [rng.randrange(3), rng.randrange(levels + 3), rng.randrange(40, 210),
                     rng.randrange(1, 25)]
    return prices, sizes, commands


def load(directory, side):
    d = Path(directory)
    script = ''
    for k, words in enumerate(side):
        write_words(d / f'in{k}', words)
        script += f'file-u64 {10 + k} {d / f"in{k}"}\n'
    return script


def finish(directory):
    d = Path(directory)
    script = ''.join(f'save-u64 result:{k} {d / f"out{k}"}\n' for k in range(2)) + 'stats\n'
    return script


def run(directory, side, commands, cuts):
    """The side after the commands, passed in chunks that end at the word offsets `cuts`, and the
    session's allocation and free counts."""
    d = Path(directory)
    script = load(directory, side)
    state = [10, 11]
    bounds = [0] + cuts + [len(commands)]
    for c, (a, b) in enumerate(zip(bounds, bounds[1:])):
        write_words(d / f'chunk{c}', commands[a:b])
        script += f'file-u64 {100 + c} {d / f"chunk{c}"}\n'
        script += ''.join(f'arg-ptr {s}\n' for s in state)
        script += f'arg-ptr {100 + c}\ncall runLevels 2\n'
        state = [1000 + 2 * c + k for k in range(2)]
        script += ''.join(f'keep {s} result:{k}\n' for k, s in enumerate(state))
    counts = session(script + finish(directory))
    return [read_words(d / f'out{k}') for k in range(2)], counts


def run_steps(directory, side, commands):
    """The side after one `applyLevel` call per command, and the session's counts."""
    d = Path(directory)
    script = load(directory, side)
    state = [10, 11]
    for c in range(len(commands) // 4):
        script += ''.join(f'arg-ptr {s}\n' for s in state)
        script += ''.join(f'arg-u64 {w}\n' for w in commands[4 * c:4 * c + 4])
        script += 'call applyLevel 2\n'
        state = [1000 + 2 * c + k for k in range(2)]
        script += ''.join(f'keep {s} result:{k}\n' for k, s in enumerate(state))
    counts = session(script + finish(directory))
    return [read_words(d / f'out{k}') for k in range(2)], counts


def main():
    rng = random.Random(7)
    failed = 0
    cases = 0
    for trial in range(40):
        prices, sizes, commands = side_and_commands(rng, rng.randrange(0, 9), rng.randrange(1, 60))
        whole = len(commands) // 4
        splits = [[], [4 * k for k in range(1, whole)],
                  sorted(4 * k for k in rng.sample(range(1, whole), min(3, whole - 1)))]
        with tempfile.TemporaryDirectory() as directory:
            one, (allocs, frees) = run(directory, [prices, sizes], commands, [])
            steps, step_counts = run_steps(directory, [prices, sizes], commands)
            for cuts in splits:
                cases += 1
                chunked, (c_allocs, c_frees) = run(directory, [prices, sizes], commands, cuts)
                # The results and one commands array per chunk stay allocated.
                counted = c_allocs - c_frees == 2 + len(cuts) + 1
                if chunked != one or not counted:
                    failed += 1
                    print(f'fail: trial {trial}, cuts {cuts}: {chunked} with {c_allocs} '
                          f'allocations and {c_frees} frees, against {one} with {allocs} and '
                          f'{frees}')
            cases += 1
            # The steps leave the results allocated, and one call also its commands array.
            counted = step_counts[0] - step_counts[1] == 2 and allocs - frees == 3
            if steps != one or not counted:
                failed += 1
                print(f'fail: trial {trial}, steps: {steps} with counts {step_counts}, against '
                      f'{one} with {(allocs, frees)}')
    print(f'chunks: {cases} cases, {failed} failed')
    sys.exit(1 if failed else 0)


main()
