#!/usr/bin/env python3
"""Test only: feed common reference-selected tokens to both complete artifacts.
Inference executes in Wasm/WGSL and parent Wasm. PyTorch supplies the reference;
NumPy comparisons and reference argmax here are not a delivered model runner.
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
from reference import digest, load_model
from wasm import WasmModel, PACKED_SHA256


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / "build/gpt2/source")
    parser.add_argument("--candidate-wasm", type=Path, required=True)
    parser.add_argument("--candidate-host", type=Path, default=ROOT / "build/tools/leanexe-packed-wgsl-host")
    parser.add_argument("--parent-wasm", type=Path, default=ROOT / "proofs/talos/.generated/gpt2_cached_step/program.wasm")
    parser.add_argument("--prompt", required=True)
    parser.add_argument("--generate", type=int, default=16)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("choose a fresh report path")
    weights = args.source / "inference/weights.bin"
    if digest(weights) != PACKED_SHA256:
        raise ValueError("packed checkpoint differs")
    tokenizer, reference = load_model(args.source)
    prompt = tokenizer.encode(args.prompt, add_special_tokens=False)
    if not prompt or not 1 <= args.generate <= 128-len(prompt):
        raise ValueError("prompt and generation must fit the 128-token context")
    tokens = list(prompt)
    rows = []
    passed = True
    started = time.monotonic()
    with WasmModel(args.parent_wasm, weights, cached=True) as parent, \
         WasmModel(args.candidate_wasm, weights, cached=True, host=args.candidate_host) as candidate:
        for step in range(args.generate):
            with torch.inference_mode():
                target = reference(torch.tensor([tokens]), use_cache=False).logits[0,-1].numpy()
            p = np.asarray(parent.infer(tokens), dtype=np.float32)
            c = np.asarray(candidate.infer(tokens), dtype=np.float32)
            reference_token = int(target.argmax())
            pe, ce = np.abs(p-target), np.abs(c-target)
            tolerance = .002 + .0001*np.abs(target)
            same_choice = int(p.argmax()) == int(c.argmax()) == reference_token
            ok = bool(np.isfinite(p).all() and np.isfinite(c).all() and
                      np.all(pe <= tolerance) and np.all(ce <= tolerance) and same_choice)
            row = {"step":step,"contextTokens":len(tokens),"token":reference_token,
                   "parentArgmax":int(p.argmax()),"candidateArgmax":int(c.argmax()),
                   "parentPytorchMaxAbs":float(pe.max()),"candidatePytorchMaxAbs":float(ce.max()),
                   "candidateParentMaxAbs":float(np.abs(c-p).max()),
                   "candidateParentUnequalWords":int(np.count_nonzero(c.view(np.uint32)!=p.view(np.uint32))),
                   "pass":ok}
            print(json.dumps(row),flush=True)
            rows.append(row); passed = passed and ok; tokens.append(reference_token)
            if reference_token == 50256:
                break
        statistics = {"parentAllocations":parent.stats,"candidateAllocations":candidate.stats,
                      "parentMemoryBytes":parent.memory_bytes,"candidateMemoryBytes":candidate.memory_bytes}
    report = {"status":"pass" if passed else "fail","candidate":"experimental parent packed FP32 Wasm with compiled WGSL matrix calls",
              "fullHybridExecutionProofEstablished":False,"parentWasmSha256":digest(args.parent_wasm),
              "candidateWasmSha256":digest(args.candidate_wasm),"weightsSha256":PACKED_SHA256,
              "torch":torch.__version__,"transformers":transformers.__version__,
              "prompt":args.prompt,"promptTokens":prompt,"tokens":tokens,"completion":tokenizer.decode(tokens),
              "tolerance":"abs(error) <= 0.002 + 0.0001*abs(PyTorch logit), plus equal greedy argmax",
              "measurements":rows,"comparedLogitsPerImplementation":50257*len(rows),
              "seconds":time.monotonic()-started,**statistics}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(report,indent=2)+"\n")
    print(report["completion"],flush=True)
    if not passed:
        raise RuntimeError(f"packed comparison failed: {args.output}")


if __name__ == "__main__":
    main()
