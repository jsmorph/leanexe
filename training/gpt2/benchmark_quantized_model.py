import argparse
import hashlib
import json
import platform
import statistics
import time
from pathlib import Path

import numpy as np
import torch

from quantized_wasm import QuantizedModel, peak_rss
from reference import MANIFEST, ROOT, digest, load_model
from wasm import HOST, PACKED_SHA256, WasmModel, run


def summarize(values):
    return {"median": statistics.median(values), "min": min(values), "max": max(values)}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--wasm", type=Path, default=ROOT / "build/gpt2-quantized-session.wasm")
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--repetitions", type=int, default=5)
    parser.add_argument("--output", type=Path, default=ROOT / "build/gpt2-124m/quantized/warm-benchmark.json")
    parser.add_argument("--grouped", action="store_true")
    args = parser.parse_args()
    if args.repetitions < 1:
        raise ValueError("Repetition count must be positive")
    evaluation_path = ROOT / "data/gpt2-quantized-v1/evaluation.json"
    evaluation = json.loads(evaluation_path.read_text())
    tokens = evaluation["prefix_tokens"]
    fp32_digest = evaluation["fp32_wasm_sha256"]
    fp32_binary = ROOT / f"proofs/artifacts/gpt2_cached_step/{fp32_digest}/program.wasm"
    fp32_weights = args.model_dir / "inference/weights.bin"
    quantized_dir = args.model_dir / ("quantized-group64" if args.grouped else "quantized")
    quantized_weights = quantized_dir / "weights.bin"
    quantized_manifest = json.loads((quantized_dir / "manifest.json").read_text())
    if digest(fp32_binary) != fp32_digest or digest(fp32_weights) != PACKED_SHA256:
        raise ValueError("FP32 baseline identity mismatch")
    if digest(quantized_weights) != quantized_manifest["weights_sha256"]:
        raise ValueError("Quantized checkpoint identity mismatch")
    _, reference = load_model(args.model_dir)
    with torch.inference_mode():
        expected = reference(torch.tensor([tokens]), use_cache=False).logits[0].numpy().copy()
    del reference
    comparisons = []
    traces = []
    output_hashes = {}
    started = time.perf_counter()
    fp32 = WasmModel(fp32_binary, fp32_weights, cached=True)
    fp32_loading_seconds = time.perf_counter() - started
    with fp32, QuantizedModel(args.wasm, quantized_weights) as quantized:
        models = {"quantized": quantized, "fp32": fp32}
        for repeat in range(args.repetitions + 1):
            durations = {name: [] for name in models}
            for position in range(len(tokens)):
                order = ("quantized", "fp32") if (repeat + position) % 2 == 0 else ("fp32", "quantized")
                outputs = {}
                for name in order:
                    started = time.perf_counter()
                    values = models[name].infer(tokens[:position + 1])
                    durations[name].append(time.perf_counter() - started)
                    outputs[name] = np.asarray(values, dtype="<f4")
                    output_hash = hashlib.sha256(outputs[name].tobytes()).hexdigest()
                    key = (name, position)
                    if repeat == 0:
                        output_hashes[key] = output_hash
                    elif output_hash != output_hashes[key]:
                        raise ValueError(f"Changed {name} logits at prefix {position + 1}, repeat {repeat}")
                if repeat == 0:
                    row = {"context": position + 1, "pytorch_argmax": int(expected[position].argmax())}
                    for name, output in outputs.items():
                        difference = output.astype(np.float64) - expected[position].astype(np.float64)
                        if name == "fp32":
                            assert np.all(np.abs(difference) <= 0.002 + 1e-4 * np.abs(expected[position]))
                        row[name] = {
                            "max_abs_difference": float(np.max(np.abs(difference))),
                            "rms_difference": float(np.sqrt(np.mean(difference * difference))),
                            "centered_rms_difference": float(np.std(difference)),
                            "argmax": int(output.argmax()), "logits_sha256": output_hashes[name, position],
                        }
                    comparisons.append(row)
            trace = {"repeat": repeat, "warmup": repeat == 0, "seconds_by_position": durations,
                     "total_seconds": {name: sum(values) for name, values in durations.items()},
                     "memory_bytes": {name: model.memory_bytes for name, model in models.items()},
                     "stats": {name: model.stats for name, model in models.items()}}
            traces.append(trace)
            print(json.dumps({key: value for key, value in trace.items() if key != "seconds_by_position"}), flush=True)
        record = {
            "schema": 1, "status": "candidate-tested-full-model-proof-pending",
            "scheme": 2 if args.grouped else 1,
            "host": platform.node(), "platform": platform.platform(),
            "cpuinfo": Path("/proc/cpuinfo").read_text(), "numpy": np.__version__, "torch": torch.__version__,
            "host_binary_sha256": digest(HOST), "evaluation_sha256": digest(evaluation_path),
            "wasmtime": run([ROOT / "build/tools/wasmtime/current/wasmtime", "--version"]).strip(),
            "canonical_nans": True,
            "source_files": {name: digest(ROOT / "training/gpt2" / name) for name in
                             ["benchmark_quantized_model.py", "quantized_wasm.py", "wasm.py", "reference.py"]},
            "quantized_wasm_sha256": digest(args.wasm), "fp32_wasm_sha256": fp32_digest,
            "quantized_weights_sha256": digest(quantized_weights), "fp32_weights_sha256": PACKED_SHA256,
            "checkpoint_sha256": MANIFEST["files"]["model.safetensors"], "tokens": tokens,
            "warmup_traces": 1, "repetitions": args.repetitions,
            "timing_scope": "Resident cached calls, logit transfer, and temporary release. Excludes loading, validation, reference comparisons, and hashing. Alternating model order at each position and repetition.",
            "loading_seconds": {"quantized": quantized.loading_seconds, "fp32": fp32_loading_seconds},
            "quantized_validation_seconds": quantized.validation_seconds,
            "peak_rss_bytes": {name: peak_rss(model.process) for name, model in models.items()},
            "warm_total_seconds": {name: summarize([row["total_seconds"][name] for row in traces[1:]])
                                   for name in models},
            "repeated_logits_bit_exact": True, "pytorch_comparisons": comparisons, "traces": traces,
        }
    record["quantized_close_stats"] = quantized.stats
    cgroup = Path("/sys/fs/cgroup") / Path("/proc/self/cgroup").read_text().strip().split(":", 2)[2].lstrip("/")
    record["execution_scope"] = {name: (cgroup / name).read_text().strip()
                                 for name in ["cpu.max", "memory.high", "memory.max", "memory.swap.max"]}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record["warm_total_seconds"]), flush=True)


if __name__ == "__main__":
    main()
