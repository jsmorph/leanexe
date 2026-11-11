# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Prints the composition of the counts of word arrays.

  uv run tests/rcv/composition.py FILE ...

Each FILE holds a word array, packed as little-endian 64-bit words: a file NAME.words that
`edges.py` or `check.py` writes, or a file of the cases of the module `rcvCount`, which the case
generator `verified-cases-rcv` writes under `build/verified/rcvCount/`.  The script computes the
count's words of each array with `result_words` of `tests/rcv/reference.py` and prints one line:
the number of arrays, of valid contests among them, and of their rounds, the number of rounds that
eliminate a batch, the candidate with the fewest votes, or a tied candidate by the order, and the
number of counts that name no winner.  The exit status is 2 when a file cannot be read or its
length is not a multiple of 8.
"""

import argparse
import importlib.util
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load_reference():
    spec = importlib.util.spec_from_file_location("reference", HERE / "reference.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("files", nargs="+", type=Path)
    args = ap.parse_args()
    reference = load_reference()
    arrays = valid = rounds = no_winner = 0
    eliminations = {1: 0, 2: 0, 3: 0}
    for path in args.files:
        try:
            data = path.read_bytes()
        except OSError as e:
            print(f"{path}: {e.strerror}", file=sys.stderr)
            return 2
        if len(data) % 8:
            print(f"{path}: {len(data)} bytes, not a multiple of 8", file=sys.stderr)
            return 2
        words = reference.unpack(data)
        result = reference.result_words(words)
        arrays += 1
        if result[0] != 1:
            continue
        valid += 1
        n, r = words[0], result[1]
        rounds += r
        for i in range(r):
            code = result[2 + i * (n + 9) + n + 6]
            if code:
                eliminations[code] += 1
        no_winner += result[-1] == 0
    print(f"{arrays} arrays, {valid} valid contests with {rounds} rounds: "
          f"{eliminations[3]} batches, {eliminations[1]} lowest eliminations, "
          f"{eliminations[2]} eliminations by order, {no_winner} counts without a winner")
    return 0


if __name__ == "__main__":
    sys.exit(main())
