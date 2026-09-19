#!/usr/bin/env python3
"""Offline full-model comparison. Candidate inference/sampling is Wasm + WGSL;
parent inference is Wasm. PyTorch and numeric comparisons are test references.
No inference runner imports this file, and it does not rebuild Lean artifacts.
"""
import argparse
import json
from pathlib import Path
import sys
import time

import numpy as np
import torch
import transformers

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "training/gpt2"))
from reference import MANIFEST, digest, load_model
from wasm import PACKED_SHA256, WasmModel


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / "build/gpt2/source")
    parser.add_argument("--wasm", type=Path,
                        default=ROOT / "proofs/talos/.generated/gpt2_cached_step/program.wasm")
    parser.add_argument("--weights", type=Path)
    parser.add_argument("--trace", type=Path, required=True)
    parser.add_argument("--trace-float", choices=["f32", "f64"], default="f64")
    parser.add_argument("--prompt", required=True)
    parser.add_argument("--candidate", required=True, help="precise implementation label for the trace")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("comparison output already exists")
    weights = args.weights or args.source / "inference/weights.bin"
    if digest(weights) != PACKED_SHA256:
        raise ValueError("parent packed weights do not match the pinned checkpoint")
    tokenizer, reference = load_model(args.source)
    prompt = tokenizer.encode(args.prompt, add_special_tokens=False)
    dtype = np.dtype([("token", "<u8"), ("logits", "<f4" if args.trace_float == "f32" else "<f8", (50257,))])
    if args.trace.stat().st_size % dtype.itemsize:
        raise ValueError("trace does not contain whole token/logit records")
    trace = np.fromfile(args.trace, dtype=dtype)
    chosen = trace["token"].astype(np.int64).tolist()
    if not chosen or any(not 0 <= token < 50257 for token in chosen) or len(prompt) + len(chosen) > 128:
        raise ValueError("invalid forced token sequence")
    sequence = prompt + chosen[:-1]
    with torch.inference_mode():
        expected = reference(torch.tensor([sequence]), use_cache=False).logits[0, len(prompt)-1:].numpy()
    rows, parent_words = [], []
    started = time.monotonic()
    valid = True
    with WasmModel(args.wasm, weights, cached=True) as model:
        for step, token in enumerate(chosen):
            parent = np.asarray(model.infer(sequence[:len(prompt)+step]), dtype=np.float32)
            candidate = trace["logits"][step].astype(np.float64)
            target = expected[step].astype(np.float64)
            parent_error = np.abs(parent.astype(np.float64) - target)
            candidate_error = np.abs(candidate - target)
            pair_error = np.abs(candidate - parent.astype(np.float64))
            tolerance = 0.002 + 1e-4 * np.abs(target)
            finite = bool(np.isfinite(candidate).all() and np.isfinite(parent).all())
            passed = bool(finite and np.all(parent_error <= tolerance) and np.all(candidate_error <= tolerance)
                          and int(candidate.argmax()) == token)
            valid = valid and passed
            row = {"step":step,"contextTokens":len(prompt)+step,"chosenToken":token,
                   "parentArgmax":int(parent.argmax()),"candidateArgmax":int(candidate.argmax()),
                   "pytorchArgmax":int(target.argmax()),"parentPytorchMaxAbs":float(parent_error.max()),
                   "candidatePytorchMaxAbs":float(candidate_error.max()),
                   "candidateParentMaxAbs":float(pair_error.max()),"pass":passed}
            rows.append(row)
            parent_words.append(parent)
            print(json.dumps(row),flush=True)
        stats = model.stats
        memory = model.memory_bytes
    parent_follows = all(row["parentArgmax"] == row["chosenToken"] for row in rows)
    reference_follows = all(row["pytorchArgmax"] == row["chosenToken"] for row in rows)
    report = {"status":"pass" if valid else "fail","candidate":args.candidate,
              "candidateTrace":str(args.trace),"parentWasm":str(args.wasm),
              "parentWasmSha256":digest(args.wasm),"weightsSha256":PACKED_SHA256,
              "checkpointSha256":MANIFEST["files"]["model.safetensors"],
              "torch":torch.__version__,"transformers":transformers.__version__,
              "prompt":args.prompt,"promptTokens":prompt,"generatedTokens":chosen,
              "candidateCompletion":tokenizer.decode(prompt+chosen),
              "parentGreedyCompletionMatchesCandidate":parent_follows,
              "pytorchGreedyCompletionMatchesCandidate":reference_follows,
              "comparedLogitsPerImplementation":len(chosen)*50257,"measurements":rows,
              "parentMemoryBytes":memory,"parentAllocatorStats":stats,
              "parentRunSeconds":time.monotonic()-started,
              "tolerance":"abs(error) <= 0.002 + 0.0001*abs(PyTorch logit)",
              "evidence":"execution tests on common token contexts; not a universal proof"}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2,ensure_ascii=False)+"\n")
    np.stack(parent_words).astype("<f4").tofile(args.output.with_suffix(".parent-f32.bin"))
    print(json.dumps({key:report[key] for key in ("status","candidateCompletion",
          "parentGreedyCompletionMatchesCandidate","pytorchGreedyCompletionMatchesCandidate",
          "comparedLogitsPerImplementation","parentRunSeconds")}),flush=True)
    if not valid:
        raise RuntimeError(f"model comparison failed; evidence: {args.output}")


if __name__ == "__main__":
    main()
