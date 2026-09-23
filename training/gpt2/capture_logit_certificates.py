import argparse
import gzip
import hashlib
import json
import struct
from pathlib import Path

import numpy as np

from quantized_wasm import QuantizedModel
from reference import ROOT, digest
from wasm import HOST, PACKED_SHA256, WasmModel


def scaled_value(word):
    exponent = (word >> 23) & 255
    fraction = word & 0x7FFFFF
    if exponent == 255:
        raise ValueError("Logit certificates require finite values")
    magnitude = fraction if exponent == 0 else (0x800000 + fraction) << (exponent - 1)
    return -magnitude if word >> 31 else magnitude


def margin_record(reference, quantized, winner, shift):
    errors = [abs(q - r - shift) for r, q in zip(reference, quantized, strict=True)]
    slacks = [reference[winner] - r - errors[winner] - errors[i]
              for i, r in enumerate(reference) if i != winner]
    return {"passes_integer_margin": min(slacks) > 0, "shift_scaled": str(shift),
            "max_error_scaled": str(max(errors)), "winner_error_scaled": str(errors[winner]),
            "min_margin_slack_scaled": str(min(slacks))}


def main():
    parser = argparse.ArgumentParser(description="Capture exact paired logit words for Lean margin checking")
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output", type=Path, default=ROOT / "build/gpt2-124m/quantized-group64/certificates")
    parser.add_argument("--evaluation", type=Path,
                        default=ROOT / "data/gpt2-quantized-v1/evaluation.json")
    args = parser.parse_args()
    evaluation_path = args.evaluation
    evaluation = json.loads(evaluation_path.read_text())
    deployment = json.loads((ROOT / "data/gpt2-quantized-v1/model.json").read_text())
    quantized_binary = ROOT / deployment["wasm_path"]
    quantized_weights = args.model_dir / "quantized-group64/weights.bin"
    fp32_binary = ROOT / f"proofs/artifacts/gpt2_cached_step/{evaluation['fp32_wasm_sha256']}/program.wasm"
    fp32_weights = args.model_dir / "inference/weights.bin"
    for path, expected in [(quantized_binary, deployment["wasm_sha256"]),
                           (quantized_weights, deployment["weights_sha256"]),
                           (fp32_binary, evaluation["fp32_wasm_sha256"]), (fp32_weights, PACKED_SHA256)]:
        if digest(path) != expected:
            raise ValueError(f"Pinned input identity mismatch: {path}")
    sequences = ([{"name": "fixed-128", "tokens": evaluation["prefix_tokens"]}]
                 if "prefix_tokens" in evaluation else [])
    sequences += [{"name": f"prompt-{i}", "prompt": case["prompt"], "tokens": case["prompt_tokens"]}
                  for i, case in enumerate(evaluation["retained_completions"] + evaluation["heldout"])]
    args.output.mkdir(parents=True, exist_ok=True)
    raw_path = args.output / "logit-pairs.bin"
    rows = []
    with (raw_path.open("wb") as stream,
          QuantizedModel(quantized_binary, quantized_weights) as quantized,
          WasmModel(fp32_binary, fp32_weights, cached=True) as fp32):
        stream.write(b"LXQLG001" + struct.pack("<II", sum(len(item["tokens"]) for item in sequences), 50257))
        for sequence, item in enumerate(sequences):
            for position in range(len(item["tokens"])):
                tokens = item["tokens"][:position + 1]
                baseline = np.asarray(fp32.infer(tokens), dtype="<f4")
                observed = np.asarray(quantized.infer(tokens), dtype="<f4")
                if baseline.shape != (50257,) or observed.shape != (50257,):
                    raise ValueError("Unexpected vocabulary shape")
                reference = [scaled_value(word) for word in baseline.view("<u4").tolist()]
                candidate = [scaled_value(word) for word in observed.view("<u4").tolist()]
                winner = max(range(50257), key=reference.__getitem__)
                observed_winner = max(range(50257), key=candidate.__getitem__)
                difference = observed.astype(np.float64) - baseline.astype(np.float64)
                stream.write(struct.pack("<III", sequence, position, winner))
                stream.write(baseline.tobytes())
                stream.write(observed.tobytes())
                row = {"sequence": sequence, "position": position, "winner": winner,
                       "quantized_winner": observed_winner,
                       "max_absolute_difference": float(np.max(np.abs(difference))),
                       "rms_difference": float(np.sqrt(np.mean(difference * difference))),
                       "fp32_logits_sha256": hashlib.sha256(baseline.tobytes()).hexdigest(),
                       "quantized_logits_sha256": hashlib.sha256(observed.tobytes()).hexdigest(),
                       "raw": margin_record(reference, candidate, winner, 0),
                       "shifted": margin_record(reference, candidate, winner, candidate[winner] - reference[winner])}
                for kind in ["raw", "shifted"]:
                    if row[kind]["passes_integer_margin"] and winner != observed_winner:
                        raise ValueError("Margin passed with different greedy choices")
                rows.append(row)
            print(json.dumps({"sequence": sequence, "positions": len(item["tokens"]),
                              "raw_passes": sum(row["raw"]["passes_integer_margin"] for row in rows if row["sequence"] == sequence),
                              "shifted_passes": sum(row["shifted"]["passes_integer_margin"] for row in rows if row["sequence"] == sequence)}), flush=True)
    compressed_path = args.output / "logit-pairs.bin.gz"
    with raw_path.open("rb") as source, compressed_path.open("wb") as destination:
        with gzip.GzipFile(filename="", mode="wb", fileobj=destination, mtime=0) as compressed:
            while chunk := source.read(1024 * 1024):
                compressed.write(chunk)
    record = {"schema": 1, "status": "captured-awaiting-lean-check",
              "bound_kind": "A posteriori exact differences between paired finite FP32 logits. Shifted bounds subtract the winning logit's common offset before comparison.",
              "scaled_unit": "2^-149", "sequences": sequences, "measurements": rows,
              "evaluation_sha256": digest(evaluation_path), "host_binary_sha256": digest(HOST),
              "source_sha256": digest(Path(__file__)), "numpy": np.__version__,
              "fp32_wasm_sha256": digest(fp32_binary), "quantized_wasm_sha256": digest(quantized_binary),
              "fp32_weights_sha256": digest(fp32_weights), "quantized_weights_sha256": digest(quantized_weights),
              "raw_bytes": raw_path.stat().st_size, "raw_sha256": digest(raw_path),
              "gzip_bytes": compressed_path.stat().st_size, "gzip_sha256": digest(compressed_path)}
    (args.output / "capture.json").write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
