import argparse
import hashlib
import json
import time
from pathlib import Path

import numpy as np

from quantized_reference import F32, QuantizedReference, word
from reference import ROOT, digest


class ActivationReference(QuantizedReference):
    def __init__(self, directory, output):
        super().__init__(directory, grouped=True)
        self.output = output
        self.groups = 0
        self.max_scale = F32(0)
        self.max_quotient = F32(0)

    def linear(self, values, name, bias=True):
        if len(values) % 64 or not np.all(np.isfinite(values)):
            raise ValueError("Invalid activation group")
        for group in values.reshape(-1, 64):
            maximum = np.max(np.abs(group))
            scale = F32(1) if maximum == 0 else np.maximum(maximum / F32(127), word(0x00800000))
            quotient = group / scale
            codes = np.rint(np.clip(quotient, F32(-127), F32(127))).astype(np.int8)
            self.output.write(group.astype("<f4").tobytes())
            self.output.write(np.asarray(scale, dtype="<f4").tobytes())
            self.output.write(codes.tobytes())
            self.groups += 1
            self.max_scale = np.maximum(self.max_scale, scale)
            self.max_quotient = np.maximum(self.max_quotient, np.max(np.abs(quotient)))
        return super().linear(values, name, bias)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output-dir", type=Path, default=ROOT / "build/gpt2-124m/quantized-group64/activations")
    args = parser.parse_args()
    evaluation_path = ROOT / "data/gpt2-quantized-v1/evaluation.json"
    evaluation = json.loads(evaluation_path.read_text())
    fixed_path = ROOT / "data/gpt2-quantized-v1/experiments/group64/prefixes.json"
    prompt_path = ROOT / "data/gpt2-quantized-v1/experiments/group64/prompts.json"
    fixed = json.loads(fixed_path.read_text())["measurements"]
    prompts = json.loads(prompt_path.read_text())["measurements"]
    sequences = [{"tokens": evaluation["prefix_tokens"], "expected": fixed}]
    for sequence, case in enumerate(evaluation["retained_completions"] + evaluation["heldout"]):
        sequences.append({"tokens": case["prompt_tokens"],
                          "expected": [row for row in prompts if row["sequence"] == sequence]})
    args.output_dir.mkdir(parents=True, exist_ok=True)
    binary = args.output_dir / "groups.bin"
    records = []
    started = time.perf_counter()
    with binary.open("wb") as output:
        model = ActivationReference(args.model_dir / "quantized-group64", output)
        for sequence, item in enumerate(sequences):
            model.cache = []
            for position, (token, expected) in enumerate(zip(item["tokens"], item["expected"], strict=True)):
                first_group = model.groups
                logits = model.step(token)
                observed = hashlib.sha256(logits.astype("<f4").tobytes()).hexdigest()
                if observed != expected["variants"]["group64"]["logits_sha256"]:
                    raise ValueError(f"Retained logits differ at sequence {sequence}, position {position}")
                records.append({"sequence": sequence, "position": position, "token": token,
                                "first_group": first_group, "groups": model.groups - first_group,
                                "logits_sha256": observed})
                if (position + 1) % 16 == 0 or position + 1 == len(item["tokens"]):
                    print(f"Checked activation capture sequence {sequence} prefix {position + 1}", flush=True)
    record = {"schema": 1, "status": "captured-awaiting-lean-check", "group_width": 64,
              "record_bytes": 324, "record_layout": "64 little-endian FP32 inputs, one FP32 scale, 64 signed bytes",
              "groups": model.groups, "coefficients": model.groups * 64, "prefixes": len(records),
              "groups_sha256": digest(binary), "groups_bytes": binary.stat().st_size,
              "max_scale": float(model.max_scale), "max_scale_bits": int(model.max_scale.view(np.uint32)),
              "max_abs_quotient": float(model.max_quotient),
              "max_abs_quotient_bits": int(model.max_quotient.view(np.uint32)),
              "weights_sha256": digest(args.model_dir / "quantized-group64/weights.bin"),
              "evaluation_sha256": digest(evaluation_path),
              "retained_hashes": {"fixed": digest(fixed_path), "prompts": digest(prompt_path)},
              "source_sha256": digest(Path(__file__)),
              "reference_sha256": digest(ROOT / "training/gpt2/quantized_reference.py"),
              "seconds": time.perf_counter() - started, "steps": records}
    (args.output_dir / "capture.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: value for key, value in record.items() if key != "steps"}), flush=True)


if __name__ == "__main__":
    main()
