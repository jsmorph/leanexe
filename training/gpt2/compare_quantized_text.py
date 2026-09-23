import argparse
import json
import time
from pathlib import Path

from transformers import AutoTokenizer

from quantized_wasm import QuantizedModel
from reference import MANIFEST, ROOT, digest
from wasm import HOST, PACKED_SHA256, WasmModel, run, sample


def generate(model, tokenizer, case, draws):
    tokens = case["prompt_tokens"].copy()
    started = time.perf_counter()
    generated = []
    for draw in draws:
        logits = model.infer(tokens)
        token = sample(logits, case["top_k"], case.get("temperature", 0.8), draw)
        generated.append(token)
        tokens.append(token)
        if token == tokenizer.eos_token_id:
            break
    return {"tokens": generated, "text": tokenizer.decode(generated),
            "stop_reason": "eos" if generated[-1] == tokenizer.eos_token_id else
                ("context_limit" if len(tokens) == 128 else "length"),
            "seconds": time.perf_counter() - started,
            "memory_bytes": model.memory_bytes, "stats": model.stats}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--wasm", type=Path, default=ROOT / "build/gpt2-quantized-session.wasm")
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--output", type=Path, default=ROOT / "build/gpt2-124m/quantized/completions.json")
    parser.add_argument("--prng-wasm", type=Path, default=ROOT / "build/prng/prng.wasm")
    parser.add_argument("--grouped", action="store_true")
    args = parser.parse_args()
    evaluation = json.loads((ROOT / "data/gpt2-quantized-v1/evaluation.json").read_text())
    fp32_digest = evaluation["fp32_wasm_sha256"]
    fp32_binary = ROOT / f"proofs/artifacts/gpt2_cached_step/{fp32_digest}/program.wasm"
    fp32_weights = args.model_dir / "inference/weights.bin"
    if digest(fp32_binary) != fp32_digest or digest(fp32_weights) != PACKED_SHA256:
        raise ValueError("FP32 baseline identity mismatch")
    for name in ("config.json", "tokenizer.json", "tokenizer_config.json"):
        if digest(args.model_dir / name) != MANIFEST["files"][name]:
            raise ValueError(f"Tokenizer file identity mismatch: {name}")
    tokenizer = AutoTokenizer.from_pretrained(args.model_dir, local_files_only=True)
    cases = evaluation["retained_completions"] + evaluation["heldout"]
    draws = []
    for case in cases:
        assert tokenizer.encode(case["prompt"]) == case["prompt_tokens"]
        count = min(case["generate"], 128 - len(case["prompt_tokens"]))
        if case["top_k"] == 1:
            draws.append([0.0] * count)
        else:
            words = json.loads(run([HOST, "call", args.prng_wasm, "generate", "array-u64",
                                    f"i64:{case['seed']}", f"i64:{count}", f"i64:{2**53}"]))
            if len(words) != count or any(type(word) is not int or not 0 <= word < 2**53 for word in words):
                raise ValueError("Lean PRNG returned invalid samples")
            draws.append([word / 2**53 for word in words])
    results = []
    print(f"Prepared shared samples for {len(cases)} completion cases", flush=True)
    quantized_dir = args.model_dir / ("quantized-group64" if args.grouped else "quantized")
    with (QuantizedModel(args.wasm, quantized_dir / "weights.bin") as quantized,
          WasmModel(fp32_binary, fp32_weights, cached=True) as fp32):
        for case, samples in zip(cases, draws, strict=True):
            quantized_result = generate(quantized, tokenizer, case, samples)
            fp32_result = generate(fp32, tokenizer, case, samples)
            common = 0
            for left, right in zip(quantized_result["tokens"], fp32_result["tokens"]):
                if left != right:
                    break
                common += 1
            result = {"case": case, "quantized": quantized_result, "fp32": fp32_result,
                      "matching_initial_tokens": common, "draws": samples}
            results.append(result)
            print(json.dumps(result), flush=True)
    record = {
        "schema": 1, "status": "candidate-tested-full-model-proof-pending",
        "scheme": 2 if args.grouped else 1,
        "quantized_wasm_sha256": digest(args.wasm), "fp32_wasm_sha256": fp32_digest,
        "quantized_weights_sha256": digest(quantized_dir / "weights.bin"),
        "fp32_weights_sha256": PACKED_SHA256, "sampling": "shared-Lean-PRNG-draws",
        "prng_wasm_sha256": digest(args.prng_wasm),
        "results": results,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
