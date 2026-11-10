# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Compares the rounds of the three counts of `rcv-stability` with the reference's.

  uv run tests/rcv/variants.py [--stability PATH] DIR ...

For each directory, the script runs `rcv-stability rounds MODE OUT DIR/*.words` for the modes
`charter`, `single`, and `county`, which write the round lines and the winner line of the
specification's count, single count, and county count (`Demos/Rcv/Variants.lean`) of each valid
contest array NAME.words to OUT/NAME.MODE.  For each array that `from_words` of
`tests/rcv/reference.py` reads as a contest, it requires each of the three files to equal the round
lines and the winner line of the reference's count in the same mode, where the reference's `single`
is the charter's count without rule 3.  The outputs go to `tmp/rcv-variants/DIR`, where DIR is the
directory's name.  The script prints each disagreement and, for each directory, the number of
arrays, of valid contests among them, and of the rounds of each count.  The exit status is 1 when
any output differs and 2 when a tool fails or a path is missing.

The default of `--stability` is `.lake/build/bin/rcv-stability`, the executable of a repository
build.
"""

import argparse
import importlib.util
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
MODES = ("charter", "single", "county")


def load_reference():
    spec = importlib.util.spec_from_file_location("reference", HERE / "reference.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--stability", default=ROOT / ".lake/build/bin/rcv-stability", type=Path)
    ap.add_argument("dirs", nargs="+", type=Path)
    args = ap.parse_args()
    for path in [args.stability, *args.dirs]:
        if not path.exists():
            print(f"{path} does not exist", file=sys.stderr)
            return 2
    reference = load_reference()
    bad = 0
    for directory in args.dirs:
        words = sorted(directory.glob("*.words"))
        out = ROOT / "tmp/rcv-variants" / directory.resolve().name
        shutil.rmtree(out, ignore_errors=True)
        out.mkdir(parents=True)
        for mode in MODES:
            done = subprocess.run([args.stability, "rounds", mode, out, *words],
                                  capture_output=True)
            if done.returncode != 0:
                print(f"rcv-stability rounds {mode}: status {done.returncode}: "
                      f"{done.stderr.decode(errors='replace').strip()}", file=sys.stderr)
                return 2
        valid = 0
        rounds = dict.fromkeys(MODES, 0)
        for path in words:
            data = path.read_bytes()
            if len(data) % 8:
                print(f"{path}: {len(data)} bytes, not a multiple of 8", file=sys.stderr)
                return 2
            contest = reference.from_words(reference.unpack(data))
            if contest is None:
                continue
            valid += 1
            name = path.name[: -len(".words")]
            for mode in MODES:
                lines = reference.round_lines(*reference.count(contest, mode))
                rounds[mode] += sum(line.startswith(b"round ") for line in lines)
                expected = b"".join(line + b"\n" for line in lines)
                got = out / f"{name}.{mode}"
                if not got.exists() or got.read_bytes() != expected:
                    bad += 1
                    print(f"{path}: rcv-stability rounds {mode} differs from the reference")
        print(f"{directory}: {len(words)} arrays, {valid} valid contests, rounds "
              + ", ".join(f"{mode} {rounds[mode]}" for mode in MODES))
    print(f"{bad} disagreements")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
