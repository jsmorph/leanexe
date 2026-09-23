import argparse
import heapq
import json
import math
from pathlib import Path
import struct
import subprocess
import sys
import time

from reference import MANIFEST, ROOT, digest


PACKED_SHA256 = "6c12f993878ad39ba4aa3b0ab58a7466f5a62651cda94464dab438339008ba1d"
MODULE = "LeanExe.Models.Gpt2.Inference"
HOST = ROOT / "build/tools/leanexe-wasmtime-host"


def run(command, timeout=180):
    result = subprocess.run([str(arg) for arg in command], cwd=ROOT, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"{command[0]} exited with status {result.returncode}:\n"
                           f"{result.stdout}{result.stderr}".rstrip())
    return result.stdout


def prepare(directory, cached=False):
    weights = directory / "inference/weights.bin"
    if not weights.exists():
        run([sys.executable, ROOT / "training/gpt2/reference.py", "export-model",
             "--model-dir", directory])
    if digest(weights) != PACKED_SHA256:
        raise ValueError("Packed FP32 weights differ from the pinned GPT-2 checkpoint")
    for name in ("config.json", "tokenizer.json", "tokenizer_config.json"):
        if digest(directory / name) != MANIFEST["files"][name]:
            raise ValueError(f"{name}: SHA-256 differs from the pinned checkpoint")
    module = "LeanExe.Models.Gpt2.Cached" if cached else MODULE
    entry = "cachedStep" if cached else "infer"
    run([ROOT / "tools/leanrun", "--timeout", "180", "lake", "build", "lean-wasm", module])
    wasm = directory / f"inference/{entry}.wasm"
    run([ROOT / "tools/leanrun", "--timeout", "60", ROOT / ".lake/build/bin/lean-wasm",
         "compile", "--module", module, "--entry", f"LeanExe.Models.Gpt2.{entry}", "--out", wasm])
    run([ROOT / "tools/build-wasmtime-host.sh"])
    return weights, wasm


def prepare_quantized(directory):
    deployment = json.loads((ROOT / "data/gpt2-quantized-v1/model.json").read_text())
    wasm = ROOT / deployment["wasm_path"]
    if digest(wasm) != deployment["wasm_sha256"]:
        raise ValueError("Quantized WASM differs from the pinned binary")
    weights = directory / "quantized-group64/weights.bin"
    if not weights.exists():
        run([sys.executable, ROOT / "training/gpt2/quantized.py", "export-model",
             "--scheme", "group64", "--model-dir", directory], timeout=600)
    if digest(weights) != deployment["weights_sha256"]:
        raise ValueError("Quantized weights differ from the pinned checkpoint export")
    for name in ("config.json", "tokenizer.json", "tokenizer_config.json"):
        if digest(directory / name) != MANIFEST["files"][name]:
            raise ValueError(f"{name}: SHA-256 differs from the pinned checkpoint")
    run([ROOT / "tools/build-wasmtime-host.sh"])
    return weights, wasm


class WasmModel:
    def __init__(self, wasm, weights, cached=False):
        if "\n" in str(weights) or "\r" in str(weights):
            raise ValueError("The weights path cannot contain a newline")
        self.weight_bytes = weights.stat().st_size
        self.cached = cached
        self.cache_pointer = 0
        self.cache_size = 0
        self.tokens = []
        self.process = subprocess.Popen([str(HOST), "session", str(wasm)], cwd=ROOT,
                                        stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                        text=True, bufsize=1)
        self.send(f"bytes-file 0 {weights}\n" + ("" if cached else "alloc 1 512\n") + "stats")
        self.stats = self.read("stats", 4)
        self.memory_bytes = 0

    def send(self, commands):
        self.process.stdin.write(commands + "\n")
        self.process.stdin.flush()

    def line(self, prefix):
        line = self.process.stdout.readline()
        if not line:
            status = self.process.wait(timeout=10)
            raise RuntimeError(f"Wasmtime session ended with status {status}")
        fields = line.rstrip("\n").split(" ")
        if fields[0] != prefix:
            raise RuntimeError(f"Expected {prefix} from Wasmtime, received {fields[0]}")
        return fields[1:]

    def read(self, prefix, count):
        fields = self.line(prefix)
        if len(fields) != count:
            raise RuntimeError(f"Expected {count} {prefix} values, received {len(fields)}")
        return [int(value) for value in fields]

    def infer(self, tokens):
        if not 1 <= len(tokens) <= 128 or any(not 0 <= token < 50257 for token in tokens):
            raise ValueError("Inference requires 1 to 128 GPT-2 token IDs")
        if self.cached:
            return self.infer_cached(tokens)
        data = struct.pack(f"<{len(tokens)}I", *tokens)
        self.send(f"write-bytes 1 0 {data.hex()}\narg-ptr 0\narg-u64 {self.weight_bytes}\n"
                  f"arg-ptr 1\narg-u64 {len(data)}\ncall infer 2")
        pointer, size = self.read("results", 2)
        return self.read_logits(pointer, size)

    def infer_cached(self, tokens):
        if len(tokens) <= len(self.tokens) or tokens[:len(self.tokens)] != self.tokens:
            if self.cache_pointer:
                self.release(self.cache_pointer)
            self.cache_pointer, self.cache_size = 0, 0
            self.tokens = []
        for token in tokens[len(self.tokens):]:
            position = len(self.tokens)
            self.send(f"arg-ptr 0\narg-u64 {self.weight_bytes}\narg-u64 {self.cache_pointer}\n"
                      f"arg-u64 {self.cache_size}\narg-u64 {token}\narg-u64 {position}\ncall cachedStep 4")
            cache, cache_size, pointer, size = self.read("results", 4)
            if cache_size != (position + 1) * 12 * 1536 * 4:
                raise RuntimeError(f"Incorrect cache size after position {position}: {cache_size}")
            if self.cache_pointer:
                self.release(self.cache_pointer)
            self.cache_pointer, self.cache_size = cache, cache_size
            self.tokens.append(token)
            logits = self.read_logits(pointer, size)
        return logits

    def release(self, pointer):
        self.send(f"arg-u64 {pointer}\ncall release 0")
        self.read("results", 0)

    def read_logits(self, pointer, size):
        if size != 50257 * 4:
            raise RuntimeError(f"Expected 50257 FP32 logits, received {size} bytes")
        self.send(f"read-memory {pointer} {size}")
        fields = self.line("memory")
        if len(fields) != 3 or int(fields[0]) != pointer or int(fields[1]) != size:
            raise RuntimeError("Wasmtime returned an unexpected memory range")
        data = bytes.fromhex(fields[2])
        if len(data) != size:
            raise RuntimeError("Wasmtime returned a truncated logit vector")
        logits = struct.unpack("<50257f", data)
        if any(not math.isfinite(value) for value in logits):
            raise RuntimeError("WASM returned a non-finite logit")
        self.release(pointer)
        self.send("stats\nmemory-size")
        self.stats = self.read("stats", 4)
        self.memory_bytes, = self.read("memory-size", 1)
        if self.stats[0] - self.stats[3] != 2:
            raise RuntimeError(f"Inference retained temporary allocations: {self.stats}")
        return logits

    def __enter__(self):
        return self

    def __exit__(self, kind, value, traceback):
        if kind is not None:
            self.process.kill()
            self.process.wait(timeout=10)
        else:
            self.send("done")
            self.process.stdin.close()
            status = self.process.wait(timeout=10)
            if status:
                raise RuntimeError(f"Wasmtime session exited with status {status}")
        self.process.stdout.close()


def sample(logits, top_k, temperature, draw):
    candidates = heapq.nlargest(top_k, range(len(logits)), key=lambda index: logits[index])
    if top_k == 1:
        return candidates[0]
    maximum = logits[candidates[0]]
    probabilities = [math.exp((logits[index] - maximum) / temperature) for index in candidates]
    target = draw * sum(probabilities)
    total = 0.0
    for index, probability in zip(candidates, probabilities):
        total += probability
        if target < total:
            return index
    return candidates[-1]


def generate(args):
    from transformers import AutoTokenizer

    directory = args.model_dir.resolve()
    if args.quantized:
        from quantized_wasm import QuantizedModel
        weights, wasm = prepare_quantized(directory)
    else:
        weights, wasm = prepare(directory, cached=not args.full)
    tokenizer = AutoTokenizer.from_pretrained(directory, local_files_only=True)
    tokens = tokenizer.encode(args.text)
    if not 1 <= len(tokens) < 128:
        raise ValueError("Generation requires a prompt of 1 to 127 GPT-2 tokens")
    prompt_tokens = tokens.copy()
    count = min(args.generate, 128 - len(tokens))
    if args.top_k > 1:
        words = run([ROOT / "tools/prng.js", args.seed, count, 2**53]).splitlines()
        if len(words) != count:
            raise RuntimeError("Lean PRNG returned the wrong number of samples")
        draws = [int(word) / 2**53 for word in words]
    else:
        draws = [0.0] * count
    started = time.monotonic()
    generated = []
    instance = QuantizedModel(wasm, weights) if args.quantized else WasmModel(wasm, weights, cached=not args.full)
    with instance as model:
        for draw in draws:
            logits = model.infer(tokens)
            token = sample(logits, args.top_k, args.temperature, draw)
            generated.append(token)
            tokens.append(token)
            if token == tokenizer.eos_token_id:
                break
        if args.logits is not None:
            args.logits.write_bytes(struct.pack("<50257f", *logits))
        stats, memory_bytes = model.stats, model.memory_bytes
    return {
        "runtime": "LeanExe/WASM INT8 group64/FP32, Wasmtime" if args.quantized else "LeanExe/WASM FP32, Wasmtime",
        "model": MANIFEST["model"],
        "revision": MANIFEST["revision"], "parameters": MANIFEST["parameters"],
        "weights_sha256": digest(weights), "wasm_sha256": digest(wasm),
        "context_limit": 128, "prompt": args.text, "prompt_tokens": prompt_tokens,
        "kv_cache": not args.full,
        "generated_tokens": generated, "completion": tokenizer.decode(generated, skip_special_tokens=True),
        "text": tokenizer.decode(tokens, skip_special_tokens=True),
        "seed": args.seed, "top_k": args.top_k, "temperature": args.temperature,
        "stop_reason": "eos" if generated[-1] == tokenizer.eos_token_id else
            ("context_limit" if len(tokens) == 128 else "length"),
        "seconds": time.monotonic() - started, "wasm_memory_bytes": memory_bytes,
        "allocations": stats[0], "frees": stats[3],
        **({"scheme": 2, "close_allocations": model.stats[0], "close_frees": model.stats[3]} if args.quantized else {}),
    }


def main():
    parser = argparse.ArgumentParser(description="Generate text with pretrained GPT-2 124M in LeanExe/WASM")
    parser.add_argument("--text", required=True)
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--generate", type=int, default=32)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--top-k", type=int, default=40)
    parser.add_argument("--temperature", type=float, default=0.8)
    parser.add_argument("--logits", type=Path, help="Save the last evaluated context's 50257 little-endian FP32 logits")
    parser.add_argument("--json", action="store_true")
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--full", action="store_true", help="Recompute the full prefix without a key/value cache")
    mode.add_argument("--quantized", action="store_true", help="Use the pinned INT8 group64/FP32 cached binary")
    args = parser.parse_args()
    if args.generate <= 0:
        parser.error("--generate must be positive")
    if not 1 <= args.top_k <= 50257:
        parser.error("--top-k must be in [1, 50257]")
    if not 0 < args.temperature < math.inf:
        parser.error("--temperature must be positive and finite")
    if not 0 <= args.seed < 2**64:
        parser.error("--seed must be a UInt64 integer")
    result = generate(args)
    print(json.dumps(result) if args.json else result["text"])


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"gpt2: {error}", file=sys.stderr)
        sys.exit(1)
