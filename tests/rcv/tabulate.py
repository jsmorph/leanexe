# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Compares the report of a canonical file from the module, native Lean, and the reference.

  uv run tests/rcv/tabulate.py [--module PATH] [--host PATH] [--tabulate PATH] DIR ...

For each file NAME.rcv in each DIR, the script computes the reference's report with `report` of
`tests/rcv/reference.py` and requires three outputs to equal it byte for byte: the export
`tabulate` of the module, run by the Wasmtime host; `rcv-tabulate report`, the specification's
`Demos.Rcv.Spec.reportFile` in native Lean; and NAME.report, when the directory holds it, which
`edges.py`, `reader_edges.py`, and `check.py` write from the reference.  The script prints each
disagreement and, for each directory, the number of files, of well-formed files among them, and of
malformed files.  The exit status is 1 when any output differs and 2 when a tool fails or a path
is missing.

The defaults are the paths of a repository build: `build/verified/rcvTabulate.wasm`, which
`tools/Emit.lean` writes from `Demos.Rcv.TabulateProgram.compiled.module`,
`build/tools/leanexe-wasmtime-host`, and `.lake/build/bin/rcv-tabulate`.
"""

import argparse
import concurrent.futures
import importlib.util
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


class ToolError(Exception):
    pass


def load_reference():
    spec = importlib.util.spec_from_file_location("reference", HERE / "reference.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(cmd):
    out = subprocess.run(cmd, capture_output=True)
    if out.returncode != 0:
        raise ToolError(f"{' '.join(map(str, cmd))}: exit status {out.returncode}: "
                        f"{out.stderr.decode(errors='replace').strip()}")
    return out.stdout


def module_report(args, path):
    text = run([args.host, "call", args.module, "tabulate", "bytes", f"bytes-file:{path}"]).decode()
    return bytes.fromhex("".join(text.split()))


def check(args, reference, path):
    data = path.read_bytes()
    expected = reference.report(data)
    outputs = [("the module's export tabulate", module_report(args, path)),
               ("rcv-tabulate report", run([args.tabulate, "report", path]))]
    saved = path.with_suffix(".report")
    if saved.exists():
        outputs.append((saved.name, saved.read_bytes()))
    problems = [f"{path}: {name} differs from the reference's report"
                for name, got in outputs if got != expected]
    well_formed = not isinstance(reference.read(data), reference.Malformed)
    return well_formed, problems


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--module", type=Path, default=ROOT / "build/verified/rcvTabulate.wasm")
    ap.add_argument("--host", type=Path, default=ROOT / "build/tools/leanexe-wasmtime-host")
    ap.add_argument("--tabulate", type=Path, default=ROOT / ".lake/build/bin/rcv-tabulate")
    ap.add_argument("dirs", nargs="+", type=Path)
    args = ap.parse_args()
    for path in [args.module, args.host, args.tabulate, *args.dirs]:
        if not path.exists():
            print(f"tabulate.py: {path} does not exist", file=sys.stderr)
            return 2
    reference = load_reference()
    differ = 0
    try:
        with concurrent.futures.ThreadPoolExecutor(8) as pool:
            for d in args.dirs:
                paths = sorted(d.glob("*.rcv"))
                results = list(pool.map(lambda p: check(args, reference, p), paths))
                good = sum(well_formed for well_formed, _ in results)
                for _, problems in results:
                    for problem in problems:
                        print(problem)
                    differ += bool(problems)
                print(f"{d}: {len(paths)} files, {good} well-formed, {len(paths) - good} malformed")
    except ToolError as e:
        print(f"tabulate.py: {e}", file=sys.stderr)
        return 2
    print(f"{differ} files with a disagreement")
    return 1 if differ else 0


if __name__ == "__main__":
    sys.exit(main())
