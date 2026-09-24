import hashlib
import json
import subprocess
from pathlib import Path

REPORT = Path(__file__).resolve().parent
ROOT = REPORT.parent.parent
DATA = ROOT / "data/gpt2-quantized-v1"
DIGEST = "9082c12c3b73aa6998a6d8ca0d97b509710e8a035afbf93587d80659ce773075"
REVISION = "c655d35b5011c1703dfd22bcceaec4e5bee17088"


def repository_bytes(relative):
    return subprocess.run(["git", "show", f"{REVISION}:{relative}"],
                          cwd=ROOT, capture_output=True, check=True).stdout


def read(relative):
    return json.loads(repository_bytes(f"data/gpt2-quantized-v1/{relative}"))


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def summarize():
    coverage = [read("certificates/coverage.json"),
                read("experiments/group64-heldout/coverage.json")]
    sets = []
    for record in coverage:
        rows = record["measurements"]
        sets.append({
            "positions": len(rows),
            "greedy_agreement": sum(r["winner"] == r["quantized_winner"] for r in rows),
            "raw_certificates": sum(r["raw"]["passes_integer_margin"] for r in rows),
            "shifted_certificates": sum(r["shifted"]["passes_integer_margin"] for r in rows),
        })
    totals = {key: sum(s[key] for s in sets) for key in sets[0]}
    assert totals == {"positions": 302, "greedy_agreement": 263,
                      "raw_certificates": 145, "shifted_certificates": 232}
    benchmark = read(f"candidates/{DIGEST}/warm-benchmark.json")
    times = benchmark["warm_total_seconds"]
    projections = read("experiments/group64/prefixes.json")["summary"]
    assert projections["per_row"]["matching_greedy_choices"] == 87
    assert projections["group64"]["matching_greedy_choices"] == 120
    model = read("model.json")
    binary = ROOT / model["wasm_path"]
    assert binary.stat().st_size == 28315
    assert digest(binary) == DIGEST
    forward = [read("certificates/forward-evaluation.json"),
               read("experiments/group64-heldout/forward-evaluation.json")]
    assert sum(r["prefixes"] for r in forward) == 302
    assert all(r["forward_margin_certificates"] == 0 for r in forward)
    return {
        "source_revision": "c655d35b5011c1703dfd22bcceaec4e5bee17088",
        "binary_sha256": DIGEST,
        "observed_certificate_sets": sets,
        "observed_certificate_totals": totals,
        "forward_certificates": 0,
        "weight_storage_reduction_percent": 100 * (1 - 127695972 / 497759232),
        "median_runtime_ratio": times["fp32"]["median"] / times["quantized"]["median"],
        "warm_linear_memory_reduction_percent": 100 * (1 - 747110400 / 1144848384),
        "measurement_scope": benchmark["timing_scope"],
    }


if __name__ == "__main__":
    inventory = json.loads((REPORT / "evidence/inventory.json").read_text())
    for item in inventory["files"]:
        content = repository_bytes(item["path"])
        assert hashlib.sha256(content).hexdigest() == item["sha256"], item["path"]
    print(json.dumps(summarize(), indent=2))
