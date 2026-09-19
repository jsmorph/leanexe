#!/usr/bin/env python3
"""Regression only: execute both artifacts on all 128 forced contexts.
Python/PyTorch provides test inputs and an independent reference, not the
delivered inference, tokenizer, or sampler implementation.
"""
import argparse
import json
from pathlib import Path
import sys
import time

import numpy as np
import torch

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "training/gpt2"))
from reference import digest, load_model
from wasm import WasmModel, PACKED_SHA256


def memory(model, pointer, size):
    model.send(f"read-memory {pointer} {size}")
    fields = model.line("memory")
    assert len(fields) == 3 and list(map(int, fields[:2])) == [pointer, size]
    data = bytes.fromhex(fields[2])
    assert len(data) == size
    return data


def state(model):
    model.send("stats\nmemory-size")
    return model.read("stats", 4), model.read("memory-size", 1)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, default=ROOT / "build/gpt2/source")
    parser.add_argument("--candidate-wasm", type=Path, required=True)
    parser.add_argument("--parent-wasm", type=Path, default=ROOT / "proofs/talos/.generated/gpt2_cached_step/program.wasm")
    parser.add_argument("--candidate-host", type=Path, default=ROOT / "build/tools/leanexe-packed-wgsl-host")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        raise ValueError("report path must be new")
    weights = args.source / "inference/weights.bin"
    assert digest(weights) == PACKED_SHA256
    tokenizer, reference = load_model(args.source)
    tokens = tokenizer.encode("Once upon a time, in a small village" +
                              ", the people gathered to tell stories about their lives." * 20)[:128]
    assert len(tokens) == 128
    with torch.inference_mode():
        expected = reference(torch.tensor([tokens]), use_cache=False).logits[0].numpy()
    rows, boundaries, invalid = [], [], []
    start = time.monotonic()
    with WasmModel(args.parent_wasm, weights, cached=True) as parent, \
         WasmModel(args.candidate_wasm, weights, cached=True, host=args.candidate_host) as candidate:
        for position in range(128):
            p = np.asarray(parent.infer(tokens[:position+1]), dtype=np.float32)
            c = np.asarray(candidate.infer(tokens[:position+1]), dtype=np.float32)
            error = np.abs(c - expected[position])
            unequal = int(np.count_nonzero(c.view(np.uint32) != p.view(np.uint32)))
            assert unequal == 0, (position, unequal)
            assert np.isfinite(c).all() and np.all(error <= .002 + .0001*np.abs(expected[position]))
            assert parent.stats == candidate.stats and parent.memory_bytes == candidate.memory_bytes
            row = {"position": position, "parentUnequalWords": unequal, "pytorchMaxAbs": float(error.max()),
                   "candidateArgmax": int(c.argmax()), "pytorchArgmax": int(expected[position].argmax())}
            rows.append(row)
            if position in [0, 1, 126, 127]:
                assert memory(parent, parent.cache_pointer, parent.cache_size) == \
                    memory(candidate, candidate.cache_pointer, candidate.cache_size)
                boundaries.append({**row, "cacheBytes": candidate.cache_size, "cacheExact": True,
                                   "stats": candidate.stats, "memoryBytes": candidate.memory_bytes})
            if position in [0, 1, 15, 31, 63, 95, 126, 127]:
                print(json.dumps(row), flush=True)
        for model in [parent, candidate]:
            before = state(model)
            for weight_size, cache_size, token, position in [
                (model.weight_bytes, model.cache_size, 0, 128),
                (model.weight_bytes, 0, 50257, 0), (model.weight_bytes, 4, 0, 0), (0, 0, 0, 0),
            ]:
                model.send(f"arg-ptr 0\narg-u64 {weight_size}\narg-u64 {model.cache_pointer}\n"
                           f"arg-u64 {cache_size}\narg-u64 {token}\narg-u64 {position}\ncall cachedStep 4")
                assert model.read("results", 4) == [0, 0, 0, 0]
                assert state(model) == before
            invalid.append({"fourCasesRejected": True, "heapStatisticsAndMemorySizePreserved": True})
        p = np.asarray(parent.infer(tokens[:1]), dtype=np.float32)
        first = np.asarray(candidate.infer(tokens[:1]), dtype=np.float32)
        replay = np.asarray(candidate.infer(tokens[:1]), dtype=np.float32)
        assert np.array_equal(p.view(np.uint32), first.view(np.uint32))
        assert np.array_equal(first.view(np.uint32), replay.view(np.uint32))
    report = {"status": "pass", "positions": 128, "logitWords": 128*50257, "parentUnequalWords": 0,
              "pytorchMaxAbs": max(r["pytorchMaxAbs"] for r in rows),
              "pytorchArgmaxDisagreements": sum(r["candidateArgmax"] != r["pytorchArgmax"] for r in rows),
              "tolerance": "abs(error) <= 0.002 + 0.0001*abs(PyTorch logit)",
              "weightsSha256": PACKED_SHA256, "candidateSha256": digest(args.candidate_wasm),
              "parentSha256": digest(args.parent_wasm), "tokens": tokens, "boundaries": boundaries,
              "invalidInputs": invalid, "cacheRestartExact": True, "measurements": rows,
              "seconds": time.monotonic()-start}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2)+"\n")
    print(f"PASS: {report['logitWords']} logit words, four cache boundaries, invalid inputs and cache restart", flush=True)


if __name__ == "__main__":
    main()
