import argparse
import hashlib
import json
import time
from pathlib import Path

import numpy as np

from diagnose_quantized import SerialReference
from quantized_reference import QuantizedReference
from reference import ROOT, digest


class NonlinearCapture:
    def linear(self, values, name, bias=True):
        output = super().linear(values, name, bias)
        if name.endswith(".mlp.c_fc"):
            self.gelu_output.write(output.astype("<f4").tobytes())
            self.gelu_count += len(output)
        return output

    def attention(self, qkv, layer):
        self.attention_output.write(qkv.astype("<f4").tobytes())
        self.attention_count += 1
        return super().attention(qkv, layer)


class QuantizedCapture(NonlinearCapture, QuantizedReference):
    def __init__(self, directory, gelu_output, attention_output):
        super().__init__(directory, grouped=True)
        self.gelu_output = gelu_output
        self.attention_output = attention_output
        self.gelu_count = self.attention_count = 0


class ReferenceCapture(NonlinearCapture, SerialReference):
    def __init__(self, directory, gelu_output, attention_output):
        super().__init__(directory)
        self.gelu_output = gelu_output
        self.attention_output = attention_output
        self.gelu_count = self.attention_count = 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "build/gpt2-124m/quantized-group64/nonlinear")
    parser.add_argument("--coverage", type=Path, default=ROOT / "data/gpt2-quantized-v1/certificates/coverage.json")
    args = parser.parse_args()
    coverage_path = args.coverage
    coverage = json.loads(coverage_path.read_text())
    args.output_dir.mkdir(parents=True, exist_ok=True)
    gelu_path = args.output_dir / "gelu.bin"
    attention_path = args.output_dir / "attention.bin"
    started = time.perf_counter()
    with gelu_path.open("wb") as gelu_output, attention_path.open("wb") as attention_output:
        quantized = QuantizedCapture(args.model_dir / "quantized-group64", gelu_output, attention_output)
        reference = ReferenceCapture(args.model_dir, gelu_output, attention_output)
        expected = iter(coverage["measurements"])
        for sequence, case in enumerate(coverage["sequences"]):
            quantized.cache = []
            reference.cache = []
            for position, token in enumerate(case["tokens"]):
                row = next(expected)
                if row["sequence"] != sequence or row["position"] != position:
                    raise ValueError("Retained prefix ordering mismatch")
                for model, key in [(quantized, "quantized_logits_sha256"), (reference, "fp32_logits_sha256")]:
                    logits = model.step(token)
                    if hashlib.sha256(logits.astype("<f4").tobytes()).hexdigest() != row[key]:
                        raise ValueError(f"Logit mismatch for {key} sequence {sequence} position {position}")
                if (position + 1) % 16 == 0 or position + 1 == len(case["tokens"]):
                    print(f"Checked nonlinear capture sequence {sequence} prefix {position + 1}", flush=True)
        if next(expected, None) is not None:
            raise ValueError("Unused retained prefix")
    inputs = np.fromfile(gelu_path, dtype="<u4")
    unique_path = args.output_dir / "gelu-unique.bin"
    unique = np.unique(inputs)
    unique.tofile(unique_path)
    record = {"schema": 1, "status": "captured-awaiting-lean-check",
              "gelu_values": quantized.gelu_count + reference.gelu_count,
              "gelu_unique_values": len(unique),
              "attention_records": quantized.attention_count + reference.attention_count,
              "attention_record_words": 2304,
              "order": "Per prefix: quantized 12 layers, then FP32 12 layers, in source order",
              "prefixes": len(coverage["measurements"]),
              "files": {path.name: {"bytes": path.stat().st_size, "sha256": digest(path)}
                        for path in [gelu_path, unique_path, attention_path]},
              "coverage_sha256": digest(coverage_path), "source_sha256": digest(Path(__file__)),
              "reference_sources": {name: digest(ROOT / "training/gpt2" / name)
                                    for name in ["quantized_reference.py", "diagnose_quantized.py"]},
              "seconds": time.perf_counter() - started}
    (args.output_dir / "capture.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
