import argparse
import json
from pathlib import Path

import numpy as np

from quantized_reference import F32, QuantizedReference, word
from reference import ROOT, digest
from wasm import PACKED_SHA256, WasmModel


def linear_serial(matrix, values, bias=None):
    result = np.zeros(matrix.shape[0], dtype=np.float32)
    for index, value in enumerate(values):
        result = result + matrix[:, index] * value
    return result + bias if bias is not None else result


def errors(left, right):
    difference = left.astype(np.float64) - right.astype(np.float64)
    return {"max_abs": float(np.max(np.abs(difference))),
            "rms": float(np.sqrt(np.mean(difference * difference)))}


class DiagnosticReference(QuantizedReference):
    def __init__(self, directory, quantized):
        path = directory / "inference/weights.bin"
        if digest(path) != PACKED_SHA256:
            raise ValueError("FP32 checkpoint identity mismatch")
        data = np.memmap(path, mode="r", dtype="<f4")
        manifest = json.loads((directory / "inference/manifest.json").read_text())
        self.weights = {}
        for record in manifest["tensors"]:
            name, offset, shape = record["name"], record["offset_words"], record["shape"]
            value = data[offset:offset + np.prod(shape)].reshape(shape)
            if name.startswith("h.") and name.endswith(".weight") and value.ndim == 2:
                value = value.T
            self.weights[name] = value
        self.weights["wte.scale"] = np.ones(50257, dtype=np.float32)
        self.quantized = quantized
        self.grouped = False
        self.cache = []
        self.records = []

    def linear(self, values, name, bias=True):
        matrix = self.weights[name + ".weight"]
        bias_values = self.weights[name + ".bias"] if bias else None
        expected = linear_serial(matrix, values, bias_values)
        maximum = np.max(np.abs(values))
        scale = F32(1) if maximum == 0 else np.maximum(maximum / F32(127), word(0x00800000))
        codes = np.rint(np.clip(values / scale, F32(-127), F32(127)))
        reconstructed = codes * scale
        activation_only = linear_serial(matrix, reconstructed, bias_values)
        qweights = self.quantized.weights[name + ".weight"].astype(np.float32)
        qweights *= self.quantized.weights[name + ".scale"][:, None]
        weight_only = linear_serial(qweights, values, bias_values)
        both = self.quantized.linear(values, name, bias)
        self.records.append({
            "position": len(self.cache), "projection": name,
            "input_max_abs": float(maximum), "input_median_abs": float(np.median(np.abs(values))),
            "input_rms": float(np.sqrt(np.mean(values.astype(np.float64)**2))),
            "input_scale": float(scale), "quantized_zero_fraction": float(np.mean(codes == 0)),
            "activation_reconstruction": errors(reconstructed, values),
            "activation_only_output": errors(activation_only, expected),
            "weight_only_output": errors(weight_only, expected),
            "both_output": errors(both, expected),
        })
        return expected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--prefixes", type=int, default=9)
    args = parser.parse_args()
    evaluation = json.loads((ROOT / "data/gpt2-quantized-v1/evaluation.json").read_text())
    if not 1 <= args.prefixes <= 128:
        raise ValueError("Diagnostic prefix count must be from 1 to 128")
    quantized = QuantizedReference(args.model_dir / "quantized")
    reference = DiagnosticReference(args.model_dir, quantized)
    binary = ROOT / f"proofs/artifacts/gpt2_cached_step/{evaluation['fp32_wasm_sha256']}/program.wasm"
    if digest(binary) != evaluation["fp32_wasm_sha256"]:
        raise ValueError("FP32 artifact identity mismatch")
    with WasmModel(binary, args.model_dir / "inference/weights.bin", cached=True) as wasm:
        for position, token in enumerate(evaluation["prefix_tokens"][:args.prefixes]):
            expected = reference.step(token)
            observed = np.asarray(wasm.infer(evaluation["prefix_tokens"][:position + 1]), dtype=np.float32)
            np.testing.assert_array_equal(expected.view(np.uint32), observed.view(np.uint32))
            print(f"Checked FP32 diagnostic reference at prefix {position + 1}", flush=True)
    record = {"schema": 1, "status": "projection-error-diagnostic",
              "fp32_wasm_sha256": digest(binary), "fp32_reference_bit_exact": True,
              "fp32_weights_sha256": PACKED_SHA256,
              "quantized_weights_sha256": digest(args.model_dir / "quantized/weights.bin"),
              "tokens": evaluation["prefix_tokens"][:args.prefixes],
              "definition": "Each projection receives its original FP32 input. Activation-only and weight-only outputs use serial FP32 dot products of reconstructed values. Both-output uses the specified integer projection.",
              "measurements": reference.records}
    output = args.model_dir / "quantized/projection-errors.json"
    output.write_text(json.dumps(record, indent=2) + "\n")
    largest = sorted(reference.records, key=lambda row: row["both_output"]["rms"], reverse=True)[:8]
    print(json.dumps(largest), flush=True)


if __name__ == "__main__":
    main()
