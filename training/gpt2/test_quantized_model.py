import argparse
import hashlib
import json
import platform
import time
from pathlib import Path

import numpy as np

from quantized_reference import QuantizedReference
from quantized_wasm import QuantizedModel, peak_rss
from reference import ROOT, digest
from wasm import HOST, PACKED_SHA256, WasmModel


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--wasm", type=Path, default=ROOT / "build/gpt2-quantized-session.wasm")
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output", type=Path, default=ROOT / "build/gpt2-124m/quantized/cached-test.json")
    parser.add_argument("--grouped", action="store_true")
    args = parser.parse_args()
    evaluation = json.loads((ROOT / "data/gpt2-quantized-v1/evaluation.json").read_text())
    fp32_digest = evaluation["fp32_wasm_sha256"]
    fp32_binary = ROOT / f"proofs/artifacts/gpt2_cached_step/{fp32_digest}/program.wasm"
    fp32_weights = args.model_dir / "inference/weights.bin"
    if digest(fp32_binary) != fp32_digest or digest(fp32_weights) != PACKED_SHA256:
        raise ValueError("FP32 baseline identity mismatch")
    quantized_dir = args.model_dir / ("quantized-group64" if args.grouped else "quantized")
    reference = QuantizedReference(quantized_dir, grouped=args.grouped)
    experiment = (json.loads((ROOT / "data/gpt2-quantized-v1/experiments/group64/prefixes.json").read_text())
                  if args.grouped else None)
    measurements = []
    with (QuantizedModel(args.wasm, quantized_dir / "weights.bin") as quantized,
          WasmModel(fp32_binary, fp32_weights, cached=True) as fp32):
        for position, token in enumerate(evaluation["prefix_tokens"]):
            expected = reference.step(token)
            started = time.perf_counter()
            observed = np.asarray(quantized.step(token), dtype=np.float32)
            quantized_seconds = time.perf_counter() - started
            np.testing.assert_array_equal(observed.view(np.uint32), expected.view(np.uint32))
            if experiment is not None:
                expected_hash = experiment["measurements"][position]["variants"]["group64"]["logits_sha256"]
                if hashlib.sha256(observed.astype("<f4").tobytes()).hexdigest() != expected_hash:
                    raise ValueError(f"Grouped logits differ from the retained experiment at prefix {position + 1}")
            quantized.send(f"read-memory {quantized.cache_pointer} {quantized.cache_size}")
            assert bytes.fromhex(quantized.line("memory")[2]) == reference.cache_bytes()
            started = time.perf_counter()
            baseline = np.asarray(fp32.infer(evaluation["prefix_tokens"][:position + 1]), dtype=np.float32)
            fp32_seconds = time.perf_counter() - started
            error = observed.astype(np.float64) - baseline.astype(np.float64)
            centered_error = error - np.mean(error)
            baseline_logs = baseline.astype(np.float64) - np.max(baseline)
            baseline_logs -= np.log(np.sum(np.exp(baseline_logs)))
            quantized_logs = observed.astype(np.float64) - np.max(observed)
            quantized_logs -= np.log(np.sum(np.exp(quantized_logs)))
            winner = int(baseline.argmax())
            row = {
                "context": position + 1,
                "max_abs_difference": float(np.max(np.abs(error))),
                "rms_difference": float(np.sqrt(np.mean(error * error))),
                "mean_difference": float(np.mean(error)),
                "centered_rms_difference": float(np.sqrt(np.mean(centered_error * centered_error))),
                "kl_fp32_to_quantized": float(np.sum(np.exp(baseline_logs) *
                                                      (baseline_logs - quantized_logs))),
                "quantized_argmax": int(observed.argmax()), "fp32_argmax": winner,
                "fp32_winning_margin": float(baseline[winner] - np.partition(baseline, -2)[-2]),
                "quantized_seconds": quantized_seconds, "fp32_seconds": fp32_seconds,
                "quantized_memory_bytes": quantized.memory_bytes, "fp32_memory_bytes": fp32.memory_bytes,
            }
            measurements.append(row)
            if position + 1 in [1, 9, 16, 32, 64, 96, 128]:
                print(json.dumps(row), flush=True)
        record = {
            "schema": 1, "status": "candidate-tested-full-model-proof-pending",
            "scheme": 2 if args.grouped else 1,
            "host": platform.node(), "platform": platform.platform(),
            "numpy": np.__version__, "host_binary_sha256": digest(HOST),
            "source_files": {name: digest(ROOT / "training/gpt2" / name) for name in
                             ["test_quantized_model.py", "quantized.py", "quantized_reference.py", "quantized_wasm.py", "wasm.py"]},
            "quantized_wasm_sha256": digest(args.wasm), "fp32_wasm_sha256": fp32_digest,
            "quantized_weights_sha256": digest(quantized_dir / "weights.bin"),
            "fp32_weights_sha256": PACKED_SHA256, "tokens": evaluation["prefix_tokens"],
            "compared_logits": len(measurements) * 50257,
            "reference_logits_bit_exact": True, "reference_caches_bit_exact": True,
            "retained_grouped_experiment_bit_exact": args.grouped,
            "max_abs_difference": max(row["max_abs_difference"] for row in measurements),
            "matching_greedy_choices": sum(row["quantized_argmax"] == row["fp32_argmax"]
                                           for row in measurements),
            "quantized_weight_bytes": quantized.weight_bytes, "fp32_weight_bytes": fp32.weight_bytes,
            "quantized_loading_seconds": quantized.loading_seconds,
            "quantized_validation_seconds": quantized.validation_seconds,
            "quantized_peak_rss_bytes": peak_rss(quantized.process),
            "fp32_peak_rss_bytes": peak_rss(fp32.process),
            "quantized_final_stats": quantized.stats, "fp32_final_stats": fp32.stats,
            "measurements": measurements,
        }
    record["quantized_close_stats"] = quantized.stats
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Compared {record['compared_logits']} quantized logits and all cached prefixes bit for bit")


if __name__ == "__main__":
    main()
