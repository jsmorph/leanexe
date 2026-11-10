# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Writes edge cases of the canonical file's reader with the reference's reports beside them.

Each case NAME gives `NAME.rcv`, a file edited from a small well-formed contest of three candidates,
two positions, and two ballots, and `NAME.report`, the reference's report of it.  The cases add to
those of `edges.py` an absent line and a final run without LF at each of lines 2 to 11, the numbers
0...01 with twenty digits, 63, 64, 2^32 - 1, 2^32, 10^10, 2^64 - 1, 2^64, 10^20 - 1, and 10^20 in
each place that holds a number, and candidate names of 3, 255, and 256 spaces.

  reader_edges.py [OUT]     write the files into OUT (default tmp/rcv-reader)
"""

import argparse
import importlib.util
from pathlib import Path

HERE = Path(__file__).resolve().parent

BASE = (b"rcv-ballots 1\ncontest c\npositions 2\ncandidates 3\ncandidate 1 listed A\n"
        b"candidate 2 listed B\ncandidate 3 excluded C\norder 1 2 3\nballots 2\n1,2\n2|3,\n")

NUMBERS = [b"00000000000000000001", b"63", b"64", b"4294967295", b"4294967296", b"10000000000",
           b"18446744073709551615", b"18446744073709551616", b"99999999999999999999",
           b"100000000000000000000"]

# Each place that holds a number: its line and the text before and after the number.
PLACES = {
    "positions": (3, b"positions ", b""),
    "candidates": (4, b"candidates ", b""),
    "index": (5, b"candidate ", b" listed A"),
    "order": (8, b"order 1 2 ", b""),
    "ballots": (9, b"ballots ", b""),
    "field": (10, b"", b",2"),
    "multiple": (10, b"1|", b",2"),
}


def load_reference():
    spec = importlib.util.spec_from_file_location("reference", HERE / "reference.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def join(lines, final_lf=True):
    return b"\n".join(lines) + (b"\n" if final_lf else b"")


def cases():
    lines = BASE.split(b"\n")[:-1]
    out = {}
    for j in range(2, len(lines) + 1):
        out[f"absent-{j}"] = join(lines[:j - 1])
        out[f"no-lf-{j}"] = join(lines[:j], final_lf=False)
    for i, number in enumerate(NUMBERS):
        for place, (j, before, after) in PLACES.items():
            edited = list(lines)
            edited[j - 1] = before + number + after
            out[f"number-{place}-{i}"] = join(edited)
    for count in (3, 255, 256):
        edited = list(lines)
        edited[4] = b"candidate 1 listed " + b" " * count
        out[f"name-spaces-{count}"] = join(edited)
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("out", nargs="?", default="tmp/rcv-reader",
                    help="output directory (default tmp/rcv-reader)")
    args = ap.parse_args()
    reference = load_reference()
    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    good = bad = 0
    for name, data in cases().items():
        (out / f"{name}.rcv").write_bytes(data)
        (out / f"{name}.report").write_bytes(reference.report(data))
        if isinstance(reference.read(data), reference.Malformed):
            bad += 1
        else:
            good += 1
    print(f"{good + bad} files, {good} well-formed, {bad} malformed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
