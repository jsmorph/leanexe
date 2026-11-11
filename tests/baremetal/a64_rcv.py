# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Runs a tabulator's AArch64 Image on canonical files that it reads over QEMU's PL011 UART and
compares each report with the reference's.

Usage: uv run tests/baremetal/a64_rcv.py --image IMAGE --native EXE --host HOST --process WASM
    [--accel tcg|kvm] [--qemu QEMU] [--timeout SECONDS] [--work WORK] [--times FILE] DIR ...

For each file NAME.rcv of each DIR, the script writes the eight bytes of the file's length, the
lowest first, and the file's bytes to an input file, and runs IMAGE on QEMU's virt machine with
1 GiB of RAM, the CPU that tests/baremetal/qemu.sh gives the accelerator, and the UART on a file
backend whose input is that file.  QEMU must exit with status 0 within SECONDS, and the UART must
show the reference's report and the status byte 0.  The reference's report is the standard output
of EXE, the module translated to C and compiled with CompCert, which must equal that of the WASI
process WASM in the Wasmtime host HOST, whose control record must be `wasi-exit 0`.

While QEMU runs, the script reads QEMU's position in the input file from /proc and the size of the
UART's output file every millisecond, and it gives four times for each file: the startup, from
QEMU's start to its read of the input's second byte, which QEMU makes once the program has read the
first, since the receiver holds one byte; the input, from there to QEMU's read of the last byte;
the computation, from there to the report's first byte; and the output, from there to QEMU's exit.
It prints a line for each run that fails and, for each directory, the number of files and of
passes, the sum of each time, and the largest input and computation times with their files.  With
--times it writes a line for each file: the directory, the name, the bytes, the four times in
seconds, and pass or fail.  The input, the UART's output, and the references' outputs of the last
run lie in WORK, tmp/a64-rcv unless set.  The exit status is 1 when a run fails and 2 when a
reference tool fails or a path is missing.
"""

import argparse
import os
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
CPUS = {"tcg": ["-cpu", "cortex-a57"], "kvm": ["-accel", "kvm", "-cpu", "host"]}


class ToolError(Exception):
    pass


def reference(args, path, work):
    native = subprocess.run([args.native, path], capture_output=True)
    if native.returncode != 0:
        raise ToolError(f"{args.native} {path}: exit status {native.returncode}")
    stdout, stderr, control = (work / "wasi.stdout", work / "wasi.stderr", work / "wasi.control")
    wasi = subprocess.run([args.host, "--stdin-file", path, "--stdout-file", stdout,
                           "--stderr-file", stderr, "--control-file", control, "run",
                           args.process], capture_output=True)
    if wasi.returncode != 0 or control.read_text() != "wasi-exit 0\n" or stderr.read_bytes():
        raise ToolError(f"{path}: the WASI process failed: {control.read_text()!r}")
    if stdout.read_bytes() != native.stdout:
        raise ToolError(f"{path}: the C executable and the WASI process disagree")
    return native.stdout


def child_of(pid):
    try:
        text = Path(f"/proc/{pid}/task/{pid}/children").read_text().split()
    except OSError:
        return None
    return int(text[0]) if text else None


def input_fd(pid, path):
    try:
        for fd in os.listdir(f"/proc/{pid}/fd"):
            try:
                if os.readlink(f"/proc/{pid}/fd/{fd}") == str(path):
                    return fd
            except OSError:
                pass
    except OSError:
        pass
    return None


def position(pid, fd):
    try:
        for line in Path(f"/proc/{pid}/fdinfo/{fd}").read_text().splitlines():
            if line.startswith("pos:"):
                return int(line.split()[1])
    except OSError:
        pass
    return None


def run_image(args, inp, out, size):
    """Runs the Image on the input file inp of size bytes, with the UART's output in out, and
    returns QEMU's exit status and the startup, input, computation, and output times."""
    out.unlink(missing_ok=True)
    cmd = ["timeout", str(args.timeout), args.qemu, "-M", "virt", *CPUS[args.accel], "-m", "1G",
           "-display", "none", "-monitor", "none", "-chardev",
           f"file,id=u0,path={out},input-path={inp}", "-serial", "chardev:u0", "-kernel",
           args.image]
    start = time.monotonic()
    with (out.parent / "qemu.stderr").open("wb") as err:
        proc = subprocess.Popen(cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                                stderr=err)
    first = last = output = None
    qemu = fd = None
    while proc.poll() is None:
        now = time.monotonic() - start
        if qemu is None:
            qemu = child_of(proc.pid)
        if qemu is not None and fd is None:
            fd = input_fd(qemu, inp)
        # The output's size is read before the position, so that output seen in a poll implies
        # that the position read after it is the input's end.
        if output is None and out.exists() and out.stat().st_size > 0:
            output = now
        if fd is not None and last is None:
            pos = position(qemu, fd)
            if pos is not None and pos >= 2 and first is None:
                first = now
            if pos is not None and pos >= size:
                last = now
        time.sleep(0.001)
    end = time.monotonic() - start
    output = end if output is None else output
    last = output if last is None else last
    first = last if first is None else first
    return proc.returncode, (first, last - first, output - last, end - output)


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--image", type=Path, required=True)
    ap.add_argument("--native", type=Path, required=True)
    ap.add_argument("--host", type=Path, required=True)
    ap.add_argument("--process", type=Path, required=True)
    ap.add_argument("--accel", choices=sorted(CPUS), default="tcg")
    ap.add_argument("--qemu", default="qemu-system-aarch64")
    ap.add_argument("--timeout", type=int, default=600)
    ap.add_argument("--work", type=Path, default=ROOT / "tmp" / "a64-rcv")
    ap.add_argument("--times", type=Path)
    ap.add_argument("dirs", nargs="+", type=Path)
    args = ap.parse_args()
    for path in [args.image, args.native, args.host, args.process, *args.dirs]:
        if not path.exists():
            print(f"a64_rcv.py: {path} does not exist", file=sys.stderr)
            return 2
    args.image = args.image.resolve()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    inp, out = work / "input", work / "uart"
    rows = []
    failed = 0
    try:
        for d in args.dirs:
            paths = sorted(d.glob("*.rcv"))
            passes = 0
            sums = [0.0, 0.0, 0.0, 0.0]
            slowest = {"input": (0.0, ""), "computation": (0.0, "")}
            for path in paths:
                data = path.read_bytes()
                expected = reference(args, path, work) + b"\x00"
                inp.write_bytes(len(data).to_bytes(8, "little") + data)
                code, times = run_image(args, inp, out, 8 + len(data))
                got = out.read_bytes() if out.exists() else b""
                ok = code == 0 and got == expected
                if ok:
                    passes += 1
                else:
                    failed += 1
                    print(f"fail: {path}: QEMU status {code}, {len(got)} bytes of output, "
                          f"{len(expected)} expected, the last {got[-1:].hex() or 'none'}")
                sums = [a + b for a, b in zip(sums, times)]
                for key, value in (("input", times[1]), ("computation", times[2])):
                    if value > slowest[key][0]:
                        slowest[key] = (value, path.name)
                rows.append((d.name, path.name, len(data), *times, "pass" if ok else "fail"))
            print(f"{d}: {len(paths)} files, {passes} pass; total startup {sums[0]:.2f} s, "
                  f"input {sums[1]:.2f} s, computation {sums[2]:.2f} s, output {sums[3]:.2f} s; "
                  f"largest input {slowest['input'][0]:.2f} s ({slowest['input'][1]}), "
                  f"largest computation {slowest['computation'][0]:.2f} s "
                  f"({slowest['computation'][1]})")
    except ToolError as e:
        print(f"a64_rcv.py: {e}", file=sys.stderr)
        return 2
    if args.times:
        with args.times.open("w") as f:
            for row in rows:
                f.write("\t".join(f"{x:.3f}" if isinstance(x, float) else str(x) for x in row)
                        + "\n")
    print(f"{failed} files fail")
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
