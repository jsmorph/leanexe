import argparse
import json
import struct
from pathlib import Path

from reference import ROOT, digest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, default=ROOT / "build/gpt2-124m/quantized-group64")
    args = parser.parse_args()
    coverage_path = ROOT / "data/gpt2-quantized-v1/certificates/coverage.json"
    coverage = json.loads(coverage_path.read_text())
    normalized = args.directory / "normalization/rows.bin"
    projected = args.directory / "projection-ranges/rows.bin"
    norm_receipt = json.loads((ROOT / "data/gpt2-quantized-v1/certificates/normalization-check.json").read_text())
    proj_receipt = json.loads((ROOT / "data/gpt2-quantized-v1/certificates/projection-check.json").read_text())
    for path, receipt in [(normalized, norm_receipt), (projected, proj_receipt)]:
        if digest(path) != receipt["rows_sha256"] or digest(coverage_path) != receipt["coverage_sha256"]:
            raise ValueError(f"Captured input identity mismatch: {path}")
    norm = normalized.read_bytes()
    proj = projected.read_bytes()
    offsets = []
    cursor = 0
    for layout in proj_receipt["layout"]:
        offsets.append(cursor + layout["input_words"] * 4)
        cursor += (layout["input_words"] + layout["output_words"]) * 4
    prefixes = len(coverage["measurements"])
    if len(norm) != prefixes * 50 * 9216 or len(proj) != prefixes * 2 * cursor:
        raise ValueError("Captured input extent mismatch")
    out = args.directory / "pointwise"
    out.mkdir(parents=True, exist_ok=True)
    def hidden(trace, model, index):
        start = (trace * 50 + model * 25 + index) * 9216
        return norm[start:start + 3072]
    def output(trace, model, index):
        start = (trace * 2 + model) * cursor + offsets[index]
        return proj[start:start + 3072]
    with (out / "embedding.bin").open("wb") as embeddings, (out / "residual.bin").open("wb") as residuals:
        for trace, row in enumerate(coverage["measurements"]):
            position = row["position"]
            token = coverage["sequences"][row["sequence"]]["tokens"][position]
            embeddings.write(struct.pack("<II", token, position))
            embeddings.write(hidden(trace, 0, 0))
            embeddings.write(hidden(trace, 1, 0))
            for layer in range(12):
                for stage in range(2):
                    for model in range(2):
                        residuals.write(hidden(trace, model, layer * 2 + stage))
                        residuals.write(output(trace, model, layer * 4 + stage * 2 + 1))
                        residuals.write(hidden(trace, model, layer * 2 + stage + 1))
    record = {"schema": 1, "status": "prepared-awaiting-lean-check", "prefixes": prefixes,
              "embedding_records": prefixes, "residual_records": prefixes * 24,
              "embedding_record_bytes": 6152, "residual_record_bytes": 18432,
              "embedding_layout": "token and position u32, quantized output, FP32 output",
              "residual_layout": "quantized left/right/output, FP32 left/right/output; each vector is 768 FP32 words",
              "order": "prefix, layer, residual stage, model",
              "source_sha256": digest(Path(__file__)), "coverage_sha256": digest(coverage_path),
              "normalization_sha256": digest(normalized), "projection_sha256": digest(projected),
              "embedding_sha256": digest(out / "embedding.bin"), "residual_sha256": digest(out / "residual.bin")}
    (out / "prepared.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
