# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Compares the count over words of the module, native Lean, and the reference.

  uv run tests/rcv/compare.py [--module PATH] [--host PATH] [--spec PATH] DIR ...

For each word array NAME.words in each DIR, packed as little-endian 64-bit words, the script
computes the reference's result words with `result_words` of `tests/rcv/reference.py` and
requires four outputs to equal them byte for byte: the export `count` of the module, run by the
Wasmtime host; `rcv-spec array`, the specification `Demos.Rcv.Spec.countArray` in native Lean;
`rcv-spec program`, the program `Demos.Rcv.Program.count` in native Lean; and NAME.result, when
the directory holds it, which `edges.py` and `check.py` write from the reference.  The module's
outputs go to `tmp/rcv-compare`.  The script prints each disagreement and, for each directory, the
number of arrays, of valid contests among them, and of their rounds.  The exit status is 1 when
any output differs and 2 when a tool fails or a path is missing.

The defaults are the paths of a repository build: `build/verified/rcvCount.wasm`, which
`tools/Emit.lean` writes from `Demos.Rcv.Program.compiled.module`,
`build/tools/leanexe-wasmtime-host`, and `.lake/build/bin/rcv-spec`.
"""

import argparse
import importlib.util
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def load_reference():
    spec = importlib.util.spec_from_file_location("reference", HERE / "reference.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(command):
    done = subprocess.run(command, capture_output=True)
    if done.returncode != 0:
        print(f"{' '.join(map(str, command))}: status {done.returncode}: "
              f"{done.stderr.decode(errors='replace').strip()}", file=sys.stderr)
        sys.exit(2)
    return done.stdout


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--module", default=ROOT / "build/verified/rcvCount.wasm", type=Path)
    ap.add_argument("--host", default=ROOT / "build/tools/leanexe-wasmtime-host", type=Path)
    ap.add_argument("--spec", default=ROOT / ".lake/build/bin/rcv-spec", type=Path)
    ap.add_argument("dirs", nargs="+", type=Path)
    args = ap.parse_args()
    for path in [args.module, args.host, args.spec, *args.dirs]:
        if not path.exists():
            print(f"{path} does not exist", file=sys.stderr)
            return 2
    reference = load_reference()
    work = ROOT / "tmp/rcv-compare"
    work.mkdir(parents=True, exist_ok=True)
    bad = 0
    for directory in args.dirs:
        arrays = valid = rounds = 0
        for words in sorted(directory.glob("*.words")):
            name = words.name[: -len(".words")]
            data = words.read_bytes()
            if len(data) % 8:
                print(f"{words}: {len(data)} bytes, not a multiple of 8", file=sys.stderr)
                return 2
            ref_words = reference.result_words(reference.unpack(data))
            ref = reference.pack(ref_words)
            out = work / f"{directory.name}-{name}.result"
            run([args.host, "call", args.module, "count", f"file-u64:{out}", f"file-u64:{words}"])
            outputs = {
                "module": out.read_bytes(),
                "rcv-spec array": run([args.spec, "array", words]),
                "rcv-spec program": run([args.spec, "program", words]),
            }
            stored = directory / f"{name}.result"
            if stored.exists():
                outputs[stored.name] = stored.read_bytes()
            differ = [label for label, got in outputs.items() if got != ref]
            if differ:
                bad += 1
                print(f"{words}: {', '.join(differ)} differ from the reference")
            arrays += 1
            if ref_words[0] == 1:
                valid += 1
                rounds += ref_words[1]
        print(f"{directory}: {arrays} arrays, {valid} valid contests with {rounds} rounds")
    print(f"{bad} arrays with a disagreement")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
