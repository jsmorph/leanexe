# /// script
# requires-python = ">=3.10"
# ///
"""Run one solve export of euler.wasm in the Wasmtime host and record the result.

Usage: uv run tools/euler-run.py WASM first|reconstructed N OUTDIR

The script calls `solve N` or `reconstructedSolve N 8` once, writes the returned words as
little-endian u64 to OUTDIR/words.u64le, and writes OUTDIR/summary.json with the wall time, the
peak resident size of the host, and the SHA-256 of the words.  It fails unless the status word is
0, the time word holds the bits of 0.8, and the word count is 4 + 2 N².
"""

import hashlib
import json
import resource
import struct
import subprocess
import sys
import time
from pathlib import Path

HOST = Path(__file__).resolve().parent.parent / "build/tools/leanexe-wasmtime-host"
END_TIME_BITS = 0x3FE999999999999A


def main() -> None:
    if len(sys.argv) != 5 or sys.argv[2] not in ("first", "reconstructed"):
        sys.exit(__doc__)
    wasm, kind, n, outdir = sys.argv[1], sys.argv[2], int(sys.argv[3]), Path(sys.argv[4])
    outdir.mkdir(parents=True, exist_ok=False)
    if kind == "first":
        call = ["solve", "array-u64", f"i64:{n}"]
    else:
        call = ["reconstructedSolve", "array-u64", f"i64:{n}", "i64:8"]
    start = time.monotonic()
    result = subprocess.run([str(HOST), "call", wasm, *call], capture_output=True, text=True)
    seconds = time.monotonic() - start
    peak_kb = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    if result.returncode != 0:
        sys.exit(f"host exited with {result.returncode}: {result.stderr.strip()}")
    words = [int(w) for w in result.stdout.strip().strip("[]").split(",")]
    data = struct.pack(f"<{len(words)}Q", *words)
    (outdir / "words.u64le").write_bytes(data)
    summary = {
        "solver": kind,
        "n": n,
        "status": words[0],
        "time_bits": f"0x{words[1]:016X}",
        "words": len(words),
        "seconds": round(seconds, 1),
        "peak_kb": peak_kb,
        "sha256": hashlib.sha256(data).hexdigest(),
    }
    (outdir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
    print(json.dumps(summary))
    if words[0] != 0 or words[1] != END_TIME_BITS or len(words) != 4 + 2 * n * n:
        sys.exit("the run did not succeed")


if __name__ == "__main__":
    main()
