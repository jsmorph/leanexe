import argparse
import json
import time
from pathlib import Path

from transformers import AutoTokenizer

from grouped_reference import ExperimentReference
from quantized_reference import QuantizedReference
from reference import MANIFEST, ROOT, digest
from wasm import sample


def generate(model, tokenizer, case, draws):
    tokens = case["prompt_tokens"].copy()
    generated = []
    started = time.perf_counter()
    for draw in draws:
        logits = model.infer(tokens)
        token = sample(logits, case["top_k"], case.get("temperature", 0.8), draw)
        generated.append(token)
        tokens.append(token)
        if token == tokenizer.eos_token_id:
            break
    stopped = "eos" if generated[-1] == tokenizer.eos_token_id else "context" if len(tokens) == 128 else "count"
    return {"tokens": generated, "text": tokenizer.decode(generated), "stopped": stopped,
            "reference_seconds": time.perf_counter() - started}


def first_difference(left, right):
    for index, (a, b) in enumerate(zip(left, right)):
        if a != b:
            return index + 1
    return min(len(left), len(right)) + 1 if len(left) != len(right) else None


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output", type=Path, default=ROOT / "build/gpt2-124m/quantized/group64-completions.json")
    args = parser.parse_args()
    original_digest = "4fab215a51e58996b78dc3b988182eadcf47532f60556db7dd5d8d35468483ac"
    baseline_path = ROOT / f"data/gpt2-quantized-v1/candidates/{original_digest}/completions.json"
    baseline = json.loads(baseline_path.read_text())
    evaluation = json.loads((ROOT / "data/gpt2-quantized-v1/evaluation.json").read_text())
    if (baseline["quantized_wasm_sha256"] != original_digest or
            baseline["fp32_wasm_sha256"] != evaluation["fp32_wasm_sha256"] or
            baseline["quantized_weights_sha256"] != digest(args.model_dir / "quantized/weights.bin")):
        raise ValueError("Completion baseline identity mismatch")
    for name in ("config.json", "tokenizer.json", "tokenizer_config.json"):
        if digest(args.model_dir / name) != MANIFEST["files"][name]:
            raise ValueError(f"Tokenizer identity mismatch: {name}")
    tokenizer = AutoTokenizer.from_pretrained(args.model_dir, local_files_only=True)
    source = QuantizedReference(args.model_dir / "quantized")
    variants = {"group64": ExperimentReference(source, grouped=True),
                "per_row_fp32_head": ExperimentReference(source, fp32_head=True)}
    results = []
    cases = evaluation["retained_completions"] + evaluation["heldout"]
    for case, original in zip(cases, baseline["results"], strict=True):
        if original["case"] != case or tokenizer.encode(case["prompt"]) != case["prompt_tokens"]:
            raise ValueError("Completion case or token IDs changed")
        if len(original["draws"]) != min(case["generate"], 128 - len(case["prompt_tokens"])):
            raise ValueError("Incorrect number of retained sampling draws")
        row = {"case": case, "draws": original["draws"], "variants": {}}
        for name, model in variants.items():
            result = generate(model, tokenizer, case, original["draws"])
            result["first_difference_from_fp32"] = first_difference(result["tokens"], original["fp32"]["tokens"])
            result["first_difference_from_per_row"] = first_difference(result["tokens"], original["quantized"]["tokens"])
            row["variants"][name] = result
        results.append(row)
        print(json.dumps(row), flush=True)
    record = {
        "schema": 1, "status": "reference-experiment", "group_size": 64,
        "baseline_record_sha256": digest(baseline_path),
        "quantized_weights_sha256": baseline["quantized_weights_sha256"],
        "sampling": "shared-retained-Lean-PRNG-draws", "prompts_previously_evaluated": True,
        "source_files": {name: digest(ROOT / "training/gpt2" / name) for name in
                         ["compare_grouped_text.py", "grouped_reference.py", "quantized_reference.py", "wasm.py"]},
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
