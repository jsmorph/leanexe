import argparse
import hashlib
import json
import time
from pathlib import Path

import numpy as np

from diagnose_quantized import SerialReference
from quantized_reference import QuantizedReference
from reference import ROOT, digest


class NormalizationCapture:
    def normalize(self, values, name):
        self.output.write(values.astype("<f4").tobytes())
        self.output.write(self.weights[name + ".weight"].astype("<f4").tobytes())
        self.output.write(self.weights[name + ".bias"].astype("<f4").tobytes())
        self.records += 1
        return super().normalize(values, name)


class QuantizedCapture(NormalizationCapture, QuantizedReference):
    def __init__(self, directory, output):
        super().__init__(directory, grouped=True)
        self.output = output
        self.records = 0


class ReferenceCapture(NormalizationCapture, SerialReference):
    def __init__(self, directory, output):
        super().__init__(directory)
        self.output = output
        self.records = 0

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "build/gpt2-124m/quantized-group64/normalization")
    parser.add_argument("--coverage", type=Path, default=ROOT / "data/gpt2-quantized-v1/certificates/coverage.json")
    args = parser.parse_args()
    coverage_path = args.coverage
    coverage = json.loads(coverage_path.read_text())
    args.output_dir.mkdir(parents=True, exist_ok=True)
    path = args.output_dir / "rows.bin"
    started = time.perf_counter()
    with path.open("wb") as output:
        quantized = QuantizedCapture(args.model_dir / "quantized-group64", output)
        reference = ReferenceCapture(args.model_dir, output)
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
                    print(f"Checked normalization capture sequence {sequence} prefix {position + 1}", flush=True)
        if next(expected, None) is not None:
            raise ValueError("Unused retained prefix")
    record = {"schema": 1, "status": "captured-awaiting-lean-check", "width": 768,
              "records": quantized.records + reference.records, "record_bytes": 9216,
              "record_layout": "768 input FP32 words, 768 gamma words, 768 beta words; little-endian",
              "order": "Per prefix: quantized 25 normalizations, then FP32 25 normalizations, in source order",
              "prefixes": len(coverage["measurements"]), "rows_sha256": digest(path),
              "rows_bytes": path.stat().st_size, "coverage_sha256": digest(coverage_path),
              "source_sha256": digest(Path(__file__)),
              "reference_sources": {name: digest(ROOT / "training/gpt2" / name)
                                    for name in ["quantized_reference.py", "diagnose_quantized.py"]},
              "seconds": time.perf_counter() - started}
    (args.output_dir / "capture.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
