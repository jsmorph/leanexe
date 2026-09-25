import argparse
import hashlib
import json
import platform
import statistics
from pathlib import Path

import numpy as np

from benchmark_quantized import Session
from reference import ROOT, digest
from wasm import HOST, run


def reference(directory, case):
    width, output_width, rows = (case[key] for key in ("input_width", "output_width", "rows"))
    if width % 64:
        raise ValueError("Grouped projection requires a multiple of 64 inputs")
    data = (directory / "weights.bin").read_bytes()
    matrix = np.frombuffer(data, dtype=np.int8, count=width * output_width,
                           offset=case["weight_offset"]).reshape(output_width, width).astype(np.int64)
    scales = np.frombuffer(data, dtype="<f4", count=output_width, offset=case["scale_offset"])
    inputs = np.fromfile(directory / "input.bin", dtype="<f4").reshape(rows, width)
    output = np.zeros((rows, output_width), dtype=np.float32)
    floor = np.array(0x00800000, dtype=np.uint32).view(np.float32)[()]
    for row, values in enumerate(inputs):
        for group in range(width // 64):
            start = group * 64
            x = values[start:start + 64]
            maximum = np.max(np.abs(x))
            scale = np.float32(1) if maximum == 0 else np.maximum(maximum / np.float32(127), floor)
            codes = np.rint(np.clip(x / scale, np.float32(-127), np.float32(127))).astype(np.int64)
            accumulator = matrix[:, start:start + 64] @ codes
            if np.max(np.abs(accumulator)) > 64 * 16129:
                raise ValueError("Grouped reference accumulator exceeds its range")
            output[row] += accumulator.astype(np.float32) * (scale * scales)
    if case["with_bias"]:
        output += np.frombuffer(data, dtype="<f4", count=output_width, offset=case["bias_offset"])
    return output.astype("<f4").tobytes()


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, default=ROOT / "build/gpt2-124m/quantized-kernels")
    parser.add_argument("--wasm", type=Path, default=ROOT / "build/gpt2-124m/quantized-kernels/group64.wasm")
    parser.add_argument("--repeats", type=int, default=7)
    args = parser.parse_args()
    if args.repeats < 3:
        raise ValueError("At least three measured repetitions are required")
    manifest_path = args.directory / "manifest.json"
    manifest = json.loads(manifest_path.read_text())
    previous = json.loads((ROOT / "data/gpt2-quantized-v1/kernels/wasm-benchmark.json").read_text())
    per_row_digest = "de0f34ec5a1c97a54f39c7664071278301923aebc663100fcc1002182ef9ab7a"
    per_row = ROOT / f"proofs/artifacts/gpt2_quantized_linear_rows/{per_row_digest}/program.wasm"
    fp32 = args.directory / "fp32.wasm"
    fp32_digest = next(row["wasm_sha256"] for row in previous["records"]
                       if row["variant"] == "fp32-output-major")
    if digest(per_row) != per_row_digest or digest(fp32) != fp32_digest:
        raise ValueError("Projection baseline identity mismatch")
    records = []
    for case in manifest["cases"]:
        directory = args.directory / case["name"]
        for name, expected in case["files"].items():
            if digest(directory / name) != expected:
                raise ValueError(f"Projection input identity mismatch: {case['name']}/{name}")
        grouped = reference(directory, case)
        fp32_result = (directory / "fp32-serial-output.bin").read_bytes()
        for variant, binary, entry in [("group64", args.wasm, "linearGroupedRows"),
                                        ("per_row", per_row, "linearRows"),
                                        ("fp32", fp32, "projectionFP32")]:
            if variant == "fp32":
                weights = directory / "fp32-output-major.bin"
                arguments = [case["input_width"], case["output_width"], 1, int(case["with_bias"])]
                expected = fp32_result
            else:
                weights = directory / "weights.bin"
                arguments = [case[key] for key in ("weight_offset", "scale_offset", "bias_offset",
                                                   "input_width", "output_width", "rows")]
                arguments.append(int(case["with_bias"]))
                expected = grouped if variant == "group64" else (directory / "quantized-output.bin").read_bytes()
            session = Session(binary, weights, directory / "input.bin")
            session.call(entry, arguments, expected)
            for _ in range(2):
                session.call(entry, arguments)
            times = [session.call(entry, arguments) for _ in range(args.repeats)]
            error = np.frombuffer(expected, dtype="<f4").astype(np.float64) - np.frombuffer(fp32_result, dtype="<f4")
            record = {"case": case["name"], "variant": variant, "wasm_sha256": digest(binary),
                      "reference_bit_exact": True, "reference_sha256": hashlib.sha256(expected).hexdigest(),
                      "seconds": times, "median_seconds": statistics.median(times),
                      "minimum_seconds": min(times), "maximum_seconds": max(times),
                      "max_abs_difference": float(np.max(np.abs(error))),
                      "rms_difference": float(np.sqrt(np.mean(error * error))), **session.close()}
            records.append(record)
            print(json.dumps(record), flush=True)
    record = {
        "schema": 1, "status": "grouped-projection-experiment-proof-pending", "group_size": 64,
        "host": platform.node(), "platform": platform.platform(),
        "cpu": run(["lscpu", "--json"]), "numpy": np.__version__,
        "wasmtime": run([ROOT / "build/tools/wasmtime/current/wasmtime", "--version"]).strip(),
        "canonical_nans": True, "host_binary_sha256": digest(HOST),
        "compiler_sha256": digest(ROOT / ".lake/build/bin/lean-wasm"),
        "kernel_manifest_sha256": digest(manifest_path), "warmup_calls": 2,
        "source_files": {name: digest(ROOT / name) for name in
                         ["LeanExe/Models/Gpt2/Quantized/Grouped.lean", "LeanExe/Models/Gpt2/Quantized/Kernel.lean",
                          "training/gpt2/benchmark_grouped.py", "training/gpt2/benchmark_quantized.py"]},
        "timing": "Resident session calls including quantization, projection, and output release, excluding loading and reference comparison",
        "records": records,
    }
    cgroup = Path("/sys/fs/cgroup") / Path("/proc/self/cgroup").read_text().strip().split(":", 2)[2].lstrip("/")
    record["execution_scope"] = {name: (cgroup / name).read_text().strip()
                                 for name in ["cpu.max", "memory.high", "memory.max", "memory.swap.max"]}
    (args.directory / "group64-benchmark.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
