import argparse
import gzip
import json
import sys
from decimal import Decimal, localcontext
from pathlib import Path

from reference import ROOT, digest


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--directory", type=Path, required=True)
    parser.add_argument("--records", type=Path, required=True)
    args = parser.parse_args()
    sys.set_int_max_str_digits(0)
    base, records = args.directory, args.records
    coverage_path = records / "coverage.json"
    coverage = json.loads(coverage_path.read_text())
    inputs = {}

    def check(relative, expected):
        path = base / relative
        found = digest(path)
        if found != expected:
            raise ValueError(f"Forward input identity mismatch: {path}")
        inputs[relative] = found

    normalization = json.loads((records / "normalization-check.json").read_text())
    projection = json.loads((records / "projection-check.json").read_text())
    pointwise = json.loads((records / "pointwise-check.json").read_text())
    attention = json.loads((records / "attention-check.json").read_text())
    for receipt in [normalization, projection, pointwise]:
        if receipt["coverage_sha256"] != digest(coverage_path):
            raise ValueError("Forward receipt coverage identity mismatch")
    if attention["capture"]["coverage_sha256"] != digest(coverage_path):
        raise ValueError("Attention coverage identity mismatch")
    check("normalization/rows.bin", normalization["rows_sha256"])
    check("normalization/ranges-ordered.txt", normalization["ranges_sha256"])
    for name in ["weights", "rows"]:
        check(f"projection-ranges/ranges.{name}.txt", projection["profiles"][name]["sha256"])
    for name in ["embedding", "residual"]:
        check(f"pointwise/ranges.{name}.txt", pointwise["profiles"][name]["sha256"])
    check("nonlinear/attention-ranges.txt", attention.get("profile", {}).get("sha256", attention.get("profile_sha256")))
    path = base / "forward-bounds.txt"
    lines = path.read_text().splitlines()
    if len(lines) != len(coverage["measurements"]):
        raise ValueError("Forward output extent mismatch")
    measurements = []
    bounds = []
    for index, (line, observed) in enumerate(zip(lines, coverage["measurements"])):
        row, sequence, position, logit, cache = map(int, line.split())
        if [row, sequence, position] != [index, observed["sequence"], observed["position"]]:
            raise ValueError("Forward output order mismatch")
        if logit < 2 ** (129 + 160):
            raise ValueError("This summary requires explicit margin evaluation for bounds below the finite-FP32 range")
        with localcontext() as context:
            context.prec = 12
            shown = format(Decimal(logit) / Decimal(2 ** 160), ".6E")
        measurements.append({"sequence": sequence, "position": position,
                             "logit_bound_approximate": shown,
                             "logit_numerator_digits": len(str(logit)),
                             "cache_numerator_digits": len(str(cache)),
                             "forward_margin_certified": False})
        bounds.append(logit)
    compressed = records / "forward-bounds.txt.gz"
    compressed.write_bytes(gzip.compress(path.read_bytes(), mtime=0))
    sources = [ROOT / "proofs/talos/lean/Project/Gpt2QuantizedCached/EvaluateForward.lean",
               ROOT / "proofs/talos/lean/Project/Gpt2QuantizedCached/Numerical/ForwardUpper.lean",
               ROOT / "proofs/talos/lean/Project/Gpt2QuantizedCached/Numerical/OperationUpper.lean",
               ROOT / "proofs/talos/lean/Project/Gpt2QuantizedCached/Numerical/NormalizationUpper.lean",
               ROOT / "proofs/talos/lean/Project/ProofKit/DyadicUpper.lean"]
    result = {"schema": 1, "status": "outward-evaluation-complete", "prefixes": len(lines),
              "fractional_bits": 160, "columns": ["index", "sequence", "position", "logit_numerator", "cache_numerator"],
              "forward_margin_certificates": 0,
              "inconclusive_reason": "Every propagated bound exceeds 2^129. Differences between finite FP32 logits are below 2^129, so no strict winning-margin condition can hold.",
              "minimum_bound": measurements[bounds.index(min(bounds))]["logit_bound_approximate"],
              "maximum_bound": measurements[bounds.index(max(bounds))]["logit_bound_approximate"],
              "bounds_sha256": digest(path), "bounds_bytes": path.stat().st_size,
              "compressed_bounds_sha256": digest(compressed), "coverage_sha256": digest(coverage_path),
              "input_sha256": inputs, "sources": {str(p.relative_to(ROOT)): digest(p) for p in sources},
              "evaluator_sha256": digest(ROOT / "proofs/talos/lean/.lake/build/bin/gpt2-forward-evaluate"),
              "theorem": "Project.Gpt2QuantizedCached.Numerical.ForwardUpper.trace_close",
              "greedy_theorem": "Project.Gpt2QuantizedCached.Numerical.ForwardUpper.choices_agree",
              "command": f"tools/leanrun --timeout 180 proofs/talos/lean/.lake/build/bin/gpt2-forward-evaluate {base} {coverage_path} {path}",
              "trust_boundary": "Kernel-checked operation and full-session bound theorems. Native Lean compiler/runtime evaluates natural-number bounds. Captured operands must equal source-recurrence intermediates. Python validates recorded identities and summarizes the output. Conditions include checked arithmetic ranges, reconstruction inequalities, finite magnitudes, retained parameter equality, valid shapes/tokens, and successful steps.",
              "measurements": measurements}
    (records / "forward-evaluation.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["prefixes", "minimum_bound", "maximum_bound", "forward_margin_certificates", "bounds_bytes"]}))


if __name__ == "__main__":
    main()
