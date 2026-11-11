# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Compares the Maine module's exports, its process, C, native Lean, and the reference's Maine mode.

  uv run tests/rcv/maine/tabulate.py [--module PATH] [--host PATH] [--maine PATH]
      [--process PATH] [--lean-process PATH] [--native PATH] DIR ...

For each canonical file NAME.rcv in each DIR, the script computes the reference's Maine report with
`report(data, "maine")` of `tests/rcv/reference.py` and requires these outputs to equal it byte for
byte: the export `tabulate` of the module, run by the Wasmtime host; `rcv-maine report`, the
specification's `Demos.Rcv.Maine.reportFile` in native Lean; `rcv-maine program-report`, the
program `Demos.Rcv.Maine.TabulateProgram.tabulate` in native Lean; and NAME.report, when the
directory holds it, which `edges.py` and `check.py` write from the reference.  With `--process`,
the standard output of the WASI process `Demos.Rcv.Maine.Process.module`, run by the Wasmtime host
with the file as its standard input, must equal it too, and its control records must be
`wasi-exit 0`.  With `--lean-process`, the same holds of `rcv-maine-process`, the native Lean
process, which must exit with status 0.  With `--native`, the output of `rcv-maine-c`, the module
translated to C and compiled with CompCert, must equal it.  For each word array
NAME.words, packed as little-endian 64-bit words, it computes the reference's Maine result words
and requires the export `count` of the module, `rcv-maine array`, `rcv-maine program-array`, and
NAME.result, when the directory holds it, to equal them.  The module's word results go to
`tmp/rcv-maine-compare`, and the runs of the processes write their standard output and control
records there.  The script prints each disagreement and, for each directory, the numbers of files,
of well-formed files, and of word arrays.  The exit status is 1 when any output differs and 2 when
a tool fails or a path is missing.

The defaults are the paths of a repository build: `build/verified/rcvMaine.wasm`, which
`tools/Emit.lean` writes from `Demos.Rcv.Maine.TabulateProgram.compiled.module`,
`build/tools/leanexe-wasmtime-host`, and `.lake/build/bin/rcv-maine`.
"""

import argparse
import concurrent.futures
import importlib.util
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent.parent


class ToolError(Exception):
    pass


def load_reference():
    spec = importlib.util.spec_from_file_location("reference", HERE.parent / "reference.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run(cmd, stdin=None):
    if stdin is None:
        out = subprocess.run(cmd, capture_output=True)
    else:
        with open(stdin, "rb") as source:
            out = subprocess.run(cmd, stdin=source, capture_output=True)
    if out.returncode != 0:
        raise ToolError(f"{' '.join(map(str, cmd))}: exit status {out.returncode}: "
                        f"{out.stderr.decode(errors='replace').strip()[-2000:]}")
    return out.stdout


def process_report(args, path, work):
    base = work / f"{path.parent.name}-{path.stem}"
    stdout, control = base.with_suffix(".stdout"), base.with_suffix(".control")
    guest_err = base.with_suffix(".stderr")
    run([args.host, "--stdin-file", path, "--stdout-file", stdout, "--stderr-file", guest_err,
         "--control-file", control, "run", args.process])
    if control.read_text() != "wasi-exit 0\n":
        raise ToolError(f"{path}: the process's control records are {control.read_text()!r}")
    if guest_err.read_bytes():
        raise ToolError(f"{path}: the process wrote to its standard error")
    return stdout.read_bytes()


def check_file(args, reference, path, work):
    data = path.read_bytes()
    expected = reference.report(data, "maine")
    text = run([args.host, "call", args.module, "tabulate", "bytes", f"bytes-file:{path}"]).decode()
    outputs = [("the module's export tabulate", bytes.fromhex("".join(text.split()))),
               ("rcv-maine report", run([args.maine, "report", path])),
               ("rcv-maine program-report", run([args.maine, "program-report", path]))]
    if args.process:
        outputs.append(("the WASI process", process_report(args, path, work)))
    if args.lean_process:
        outputs.append(("rcv-maine-process", run([args.lean_process], stdin=path)))
    if args.native:
        outputs.append(("rcv-maine-c", run([args.native, path])))
    saved = path.with_suffix(".report")
    if saved.exists():
        outputs.append((saved.name, saved.read_bytes()))
    problems = [f"{path}: {name} differs from the reference's report"
                for name, got in outputs if got != expected]
    well_formed = not isinstance(reference.read(data), reference.Malformed)
    return well_formed, problems


def check_words(args, reference, path, work):
    data = path.read_bytes()
    if len(data) % 8:
        raise ToolError(f"{path}: {len(data)} bytes, not a multiple of 8")
    expected = reference.pack(reference.result_words(reference.unpack(data), maine=True))
    out = work / f"{path.parent.name}-{path.stem}.result"
    run([args.host, "call", args.module, "count", f"file-u64:{out}", f"file-u64:{path}"])
    outputs = [("the module's export count", out.read_bytes()),
               ("rcv-maine array", run([args.maine, "array", path])),
               ("rcv-maine program-array", run([args.maine, "program-array", path]))]
    saved = path.with_suffix(".result")
    if saved.exists():
        outputs.append((saved.name, saved.read_bytes()))
    return [f"{path}: {name} differs from the reference's result words"
            for name, got in outputs if got != expected]


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--module", type=Path, default=ROOT / "build/verified/rcvMaine.wasm")
    ap.add_argument("--host", type=Path, default=ROOT / "build/tools/leanexe-wasmtime-host")
    ap.add_argument("--maine", type=Path, default=ROOT / ".lake/build/bin/rcv-maine")
    ap.add_argument("--process", type=Path)
    ap.add_argument("--lean-process", type=Path)
    ap.add_argument("--native", type=Path)
    ap.add_argument("--jobs", type=int, default=4)
    ap.add_argument("dirs", nargs="+", type=Path)
    args = ap.parse_args()
    optional = [p for p in (args.process, args.lean_process, args.native) if p is not None]
    for path in [args.module, args.host, args.maine, *optional, *args.dirs]:
        if not path.exists():
            print(f"tabulate.py: {path} does not exist", file=sys.stderr)
            return 2
    reference = load_reference()
    work = ROOT / "tmp/rcv-maine-compare"
    work.mkdir(parents=True, exist_ok=True)
    differ = 0
    try:
        with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
            for d in args.dirs:
                files = sorted(d.glob("*.rcv"))
                results = list(pool.map(lambda p: check_file(args, reference, p, work), files))
                good = sum(well_formed for well_formed, _ in results)
                for _, problems in results:
                    for problem in problems:
                        print(problem)
                    differ += bool(problems)
                arrays = sorted(d.glob("*.words"))
                for problems in pool.map(lambda p: check_words(args, reference, p, work), arrays):
                    for problem in problems:
                        print(problem)
                    differ += bool(problems)
                print(f"{d}: {len(files)} files, {good} well-formed, "
                      f"{len(files) - good} malformed, {len(arrays)} word arrays")
    except ToolError as e:
        print(f"tabulate.py: {e}", file=sys.stderr)
        return 2
    print(f"{differ} files or arrays with a disagreement")
    return 1 if differ else 0


if __name__ == "__main__":
    sys.exit(main())
