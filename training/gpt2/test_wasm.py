import json
import struct
import time

import numpy as np
import torch

from reference import MANIFEST, ROOT, load_model
from wasm import WasmModel, digest, prepare


def main():
    directory = ROOT / "build/gpt2-124m"
    tokenizer, reference = load_model(directory)
    prompt = "Once upon a time, in a small village"
    tokens = tokenizer.encode(prompt + ", the people gathered to tell stories about their lives." * 20)[:128]
    assert len(tokens) == 128
    with torch.inference_mode():
        expected = reference(torch.tensor([tokens]), use_cache=False).logits[0].numpy()
    weights, cached_wasm = prepare(directory, cached=True)
    differences = []
    maximum = 0.0
    started = time.monotonic()
    with WasmModel(cached_wasm, weights, cached=True) as model:
        for position in range(128):
            logits = model.infer(tokens[:position + 1])
            actual = np.asarray(logits, dtype=np.float32)
            error = np.abs(actual - expected[position])
            assert np.all(error <= 0.002 + 1e-4 * np.abs(expected[position])), (position, float(error.max()))
            maximum = max(maximum, float(error.max()))
            if position == 8:
                nine_token_logits = struct.pack("<50257f", *logits)
            if position + 1 in [1, 9, 16, 32, 64, 96, 128]:
                row = {"context": position + 1, "max_abs_difference": float(error.max()),
                       "wasm_argmax": int(actual.argmax()), "pytorch_argmax": int(expected[position].argmax()),
                       "wasm_memory_bytes": model.memory_bytes}
                differences.append(row)
                print(json.dumps(row), flush=True)
        seconds = time.monotonic() - started
        allocations, _, _, frees = model.stats
        memory_bytes = model.memory_bytes
        for weight_size, cache_size, token, position in [
            (model.weight_bytes, model.cache_size, 0, 128),
            (model.weight_bytes, 0, 50257, 0),
            (model.weight_bytes, 4, 0, 0),
            (0, 0, 0, 0),
        ]:
            model.send(f"arg-ptr 0\narg-u64 {weight_size}\narg-u64 {model.cache_pointer}\n"
                       f"arg-u64 {cache_size}\narg-u64 {token}\narg-u64 {position}\ncall cachedStep 4")
            assert model.read("results", 4) == [0, 0, 0, 0]
        first = model.infer(tokens[:1])
        assert first == model.infer(tokens[:1]), "Resetting and replaying a context must preserve logits"
    _, full_wasm = prepare(directory)
    with WasmModel(full_wasm, weights) as model:
        full = struct.pack("<50257f", *model.infer(tokens[:9]))
    assert full == nine_token_logits, "Cached and full-prefix WASM logits must match bit-for-bit"
    record = {
        "checkpoint_sha256": MANIFEST["files"]["model.safetensors"],
        "cached_wasm_sha256": digest(cached_wasm), "full_wasm_sha256": digest(full_wasm),
        "tokens": tokens, "compared_logits": 128 * 50257,
        "max_abs_difference": maximum, "cached_full_nine_token_exact": True,
        "context_boundary_and_invalid_inputs": True, "context_reset_exact": True,
        "seconds": seconds, "wasm_memory_bytes": memory_bytes,
        "allocations": allocations, "frees": frees, "measurements": differences,
    }
    path = directory / "inference/cached-test.json"
    path.write_text(json.dumps(record, indent=2) + "\n")
    print(f"Compared {record['compared_logits']} cached logits across contexts 1 to 128; max difference {maximum}")


if __name__ == "__main__":
    main()
