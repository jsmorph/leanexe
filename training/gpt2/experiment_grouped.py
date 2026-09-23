import argparse
import hashlib
import json
import time
from pathlib import Path

import numpy as np

from grouped_reference import ExperimentReference
from quantized_reference import QuantizedReference
from quantized_wasm import QuantizedModel
from reference import ROOT, digest
from wasm import HOST, PACKED_SHA256, WasmModel


def compare(observed, baseline):
    error = observed.astype(np.float64) - baseline.astype(np.float64)
    expected_logs = baseline.astype(np.float64) - np.max(baseline)
    expected_logs -= np.log(np.sum(np.exp(expected_logs)))
    observed_logs = observed.astype(np.float64) - np.max(observed)
    observed_logs -= np.log(np.sum(np.exp(observed_logs)))
    return {
        "max_abs_difference": float(np.max(np.abs(error))),
        "rms_difference": float(np.sqrt(np.mean(error * error))),
        "mean_difference": float(np.mean(error)), "centered_rms_difference": float(np.std(error)),
        "kl_fp32_to_variant": float(np.sum(np.exp(expected_logs) * (expected_logs - observed_logs))),
        "argmax": int(observed.argmax()),
        "logits_sha256": hashlib.sha256(observed.astype("<f4").tobytes()).hexdigest(),
    }


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output", type=Path, default=ROOT / "build/gpt2-124m/quantized/group64-prefixes.json")
    parser.add_argument("--prompts", action="store_true")
    args = parser.parse_args()
    evaluation_path = ROOT / "data/gpt2-quantized-v1/evaluation.json"
    evaluation = json.loads(evaluation_path.read_text())
    original_digest = "4fab215a51e58996b78dc3b988182eadcf47532f60556db7dd5d8d35468483ac"
    original = ROOT / f"data/gpt2-quantized-v1/candidates/{original_digest}/program.wasm"
    fp32_digest = evaluation["fp32_wasm_sha256"]
    fp32_binary = ROOT / f"proofs/artifacts/gpt2_cached_step/{fp32_digest}/program.wasm"
    fp32_weights = args.model_dir / "inference/weights.bin"
    quantized_weights = args.model_dir / "quantized/weights.bin"
    if digest(original) != original_digest or digest(fp32_binary) != fp32_digest:
        raise ValueError("Baseline binary identity mismatch")
    if digest(fp32_weights) != PACKED_SHA256:
        raise ValueError("FP32 checkpoint identity mismatch")
    source = QuantizedReference(args.model_dir / "quantized")
    variants = {"group64": ExperimentReference(source, grouped=True),
                "per_row_fp32_head": ExperimentReference(source, fp32_head=True)}
    sequences = ([{"prompt": case["prompt"], "tokens": case["prompt_tokens"]}
                  for case in evaluation["retained_completions"] + evaluation["heldout"]]
                 if args.prompts else [{"tokens": evaluation["prefix_tokens"]}])
    measurements = []
    started = time.perf_counter()
    with (QuantizedModel(original, quantized_weights) as per_row,
          WasmModel(fp32_binary, fp32_weights, cached=True) as fp32):
        for sequence, item in enumerate(sequences):
            for position in range(len(item["tokens"])):
                tokens = item["tokens"][:position + 1]
                baseline = np.asarray(fp32.infer(tokens), dtype=np.float32)
                outputs = {"per_row": np.asarray(per_row.infer(tokens), dtype=np.float32)}
                outputs.update({name: model.infer(tokens) for name, model in variants.items()})
                row = {"sequence": sequence, "context": position + 1, "fp32_argmax": int(baseline.argmax()),
                       "variants": {name: compare(values, baseline) for name, values in outputs.items()}}
                measurements.append(row)
                if position + 1 == len(item["tokens"]) or (not args.prompts and position + 1 in [1, 9, 16, 32, 64, 96]):
                    print(json.dumps(row), flush=True)
    summary = {}
    for name in ["per_row", *variants]:
        rows = [row["variants"][name] for row in measurements]
        summary[name] = {
            "matching_greedy_choices": sum(row["variants"][name]["argmax"] == row["fp32_argmax"]
                                           for row in measurements),
            "max_abs_difference": max(row["max_abs_difference"] for row in rows),
            "max_centered_rms_difference": max(row["centered_rms_difference"] for row in rows),
            "median_kl": float(np.median([row["kl_fp32_to_variant"] for row in rows])),
            "max_kl": max(row["kl_fp32_to_variant"] for row in rows),
        }
    record = {
        "schema": 1, "status": "reference-experiment", "group_size": 64,
        "definition": "Independent scales and int32 dots for consecutive 64-coordinate activation groups. FP32 scale products, FP32 rescaling, FP32 addition in increasing group order from positive zero, then one bias addition. Unchanged per-output weight scales and quantized embedding.",
        "control": "Per-row transformer projections with serial FP32 vocabulary dot products using FP32-reconstructed quantized weights.",
        "quantized_weights_sha256": digest(quantized_weights), "fp32_weights_sha256": PACKED_SHA256,
        "per_row_wasm_sha256": original_digest, "fp32_wasm_sha256": fp32_digest,
        "evaluation_sha256": digest(evaluation_path), "host_binary_sha256": digest(HOST),
        "numpy": np.__version__,
        "source_files": {name: digest(ROOT / "training/gpt2" / name) for name in
                         ["experiment_grouped.py", "grouped_reference.py", "quantized_reference.py", "quantized_wasm.py", "wasm.py"]},
        "sequences": sequences, "compared_prefixes": len(measurements),
        "summary": summary, "measurements": measurements,
        "experiment_seconds": time.perf_counter() - started,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(summary), flush=True)


if __name__ == "__main__":
    main()
