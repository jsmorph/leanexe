import argparse
import json
import platform
import statistics
import subprocess
import time
from pathlib import Path

from reference import ROOT, digest
from wasm import HOST, run


class Session:
    def __init__(self, wasm, weights, input_):
        started = time.perf_counter()
        self.process = subprocess.Popen([str(HOST), "session", str(wasm)], cwd=ROOT,
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        text=True, bufsize=1)
        self.weights_size = weights.stat().st_size
        self.input_size = input_.stat().st_size
        self.send(f"bytes-file 0 {weights}\nbytes-file 1 {input_}\nstats")
        self.read("stats", 4)
        self.loading_seconds = time.perf_counter() - started

    def send(self, commands):
        self.process.stdin.write(commands + "\n")
        self.process.stdin.flush()

    def read(self, prefix, count):
        line = self.process.stdout.readline()
        if not line:
            raise RuntimeError(f"Wasmtime session ended with status {self.process.wait(timeout=10)}")
        fields = line.rstrip("\n").split(" ")
        if fields[0] != prefix or len(fields) != count + 1:
            raise RuntimeError(f"Expected {prefix} with {count} fields, received {line[:200]}")
        return fields[1:]

    def call(self, entry, arguments, expected=None):
        started = time.perf_counter()
        self.send(f"arg-ptr 0\narg-u64 {self.weights_size}\narg-ptr 1\narg-u64 {self.input_size}\n" +
                  "".join(f"arg-u64 {argument}\n" for argument in arguments) + f"call {entry} 2")
        pointer, size = map(int, self.read("results", 2))
        if expected is not None:
            self.send(f"read-memory {pointer} {size}")
            address, length, data = self.read("memory", 3)
            if int(address) != pointer or int(length) != size or bytes.fromhex(data) != expected:
                raise ValueError(f"{entry} differs from the specified projection reference")
        self.send(f"arg-u64 {pointer}\ncall release 0")
        self.read("results", 0)
        return time.perf_counter() - started

    def close(self):
        self.send("stats\nmemory-size")
        allocations, retains, releases, frees = map(int, self.read("stats", 4))
        memory = int(self.read("memory-size", 1)[0])
        if allocations - frees != 2:
            raise ValueError(f"Projection session retained {allocations - frees} buffers")
        status = Path(f"/proc/{self.process.pid}/status").read_text().splitlines()
        peak_rss = next(int(line.split()[1]) * 1024 for line in status if line.startswith("VmHWM:"))
        self.send("arg-ptr 0\ncall release 0\narg-ptr 1\ncall release 0\nstats\ndone")
        self.read("results", 0)
        self.read("results", 0)
        final = list(map(int, self.read("stats", 4)))
        if final[0] != final[3]:
            raise ValueError("Projection session leaked an input buffer")
        self.process.stdin.close()
        if self.process.wait(timeout=10) != 0:
            raise RuntimeError("Wasmtime session failed during cleanup")
        return {"allocations": allocations, "retains": retains, "releases": releases,
                "frees": frees, "wasm_memory_bytes": memory, "process_peak_rss_bytes": peak_rss}


def main():
    parser = argparse.ArgumentParser(description="Measure scalar GPT-2 quantized projection cases")
    parser.add_argument("--directory", type=Path, default=ROOT / "build/gpt2-124m/quantized-kernels")
    parser.add_argument("--repeats", type=int, default=7)
    args = parser.parse_args()
    if args.repeats < 3:
        parser.error("At least three measured repetitions are required")
    manifest = json.loads((args.directory / "manifest.json").read_text())
    for case in manifest["cases"]:
        for name, expected in case["files"].items():
            if digest(args.directory / case["name"] / name) != expected:
                raise ValueError(f"{case['name']}/{name}: digest mismatch")
    quantized = "LeanExe.Models.Gpt2.Quantized.Kernel"
    baseline = "LeanExe.Examples.QuantizedKernel"
    run([ROOT / "tools/leanrun", "--timeout", "300s", "lake", "build", "lean-wasm", quantized, baseline],
        timeout=330)
    binaries = {}
    for name, module, entry in [
        ("quantized", quantized, "LeanExe.Models.Gpt2.Quantized.linearRows"),
        ("fp32", baseline, f"{baseline}.projectionFP32"),
    ]:
        binary = args.directory / f"{name}.wasm"
        run([ROOT / "tools/leanrun", "--timeout", "60s", ROOT / ".lake/build/bin/lean-wasm",
             "compile", "--module", module, "--entry", entry, "--out", binary])
        binaries[name] = binary
    run([ROOT / "tools/build-wasmtime-host.sh"])
    records = []
    for case in manifest["cases"]:
        directory = args.directory / case["name"]
        for variant in ("quantized", "fp32-input-major", "fp32-output-major"):
            is_quantized = variant == "quantized"
            binary = binaries["quantized" if is_quantized else "fp32"]
            weights = directory / ("weights.bin" if is_quantized else f"{variant}.bin")
            if is_quantized:
                entry = "linearRows"
                arguments = [case[key] for key in ("weight_offset", "scale_offset", "bias_offset",
                                                   "input_width", "output_width", "rows")]
            else:
                entry = "projectionFP32"
                arguments = [case["input_width"], case["output_width"], int(variant.endswith("output-major"))]
            arguments.append(int(case["with_bias"]))
            expected = (directory / ("quantized-output.bin" if is_quantized else "fp32-serial-output.bin")).read_bytes()
            session = Session(binary, weights, directory / "input.bin")
            session.call(entry, arguments, expected)
            for _ in range(2):
                session.call(entry, arguments)
            times = [session.call(entry, arguments) for _ in range(args.repeats)]
            record = {"case": case["name"], "variant": variant, "exact_reference": True,
                      "wasm_sha256": digest(binary), "weight_bytes": weights.stat().st_size,
                      "loading_seconds": session.loading_seconds, "seconds": times,
                      "median_seconds": statistics.median(times),
                      "minimum_seconds": min(times), "maximum_seconds": max(times), **session.close()}
            records.append(record)
            print(json.dumps(record), flush=True)
    report = {
        "schema": 1, "status": "execution-measurement-proof-pending",
        "checkpoint_sha256": manifest["checkpoint_sha256"],
        "source_revision": run(["git", "rev-parse", "HEAD"]).strip(),
        "compiler_sha256": digest(ROOT / ".lake/build/bin/lean-wasm"),
        "source_files": {str(path.relative_to(ROOT)): digest(path)
                         for path in sorted((ROOT / "LeanExe").rglob("*.lean"))},
        "kernel_manifest_sha256": digest(args.directory / "manifest.json"),
        "machine": platform.uname()._asdict(), "cpu": run(["lscpu", "--json"]),
        "wasmtime": run([ROOT / "build/tools/wasmtime/current/wasmtime", "--version"]).strip(),
        "canonical_nans": True, "warmup_calls": 2,
        "timing": "Resident session round trip including quantization, projection, and buffer release",
        "records": records,
    }
    (args.directory / "wasm-benchmark.json").write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
