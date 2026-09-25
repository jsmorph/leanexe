import time
from pathlib import Path

from wasm import WasmModel


def peak_rss(process):
    lines = Path(f"/proc/{process.pid}/status").read_text().splitlines()
    return next(int(line.split()[1]) * 1024 for line in lines if line.startswith("VmHWM:"))


class InferenceStatusError(RuntimeError):
    def __init__(self, status, position):
        self.status = status
        self.position = position
        super().__init__(f"Quantized inference returned status {status} at position {position}")


class QuantizedModel(WasmModel):
    def __init__(self, wasm, weights):
        started = time.perf_counter()
        super().__init__(wasm, weights, cached=True)
        self.loading_seconds = time.perf_counter() - started
        self.closed = False
        started = time.perf_counter()
        try:
            self.send(f"arg-ptr 0\narg-u64 {self.weight_bytes}\ncall validateModel 1")
            status, = self.read("results", 1)
        except BaseException:
            self.terminate()
            raise
        self.validation_seconds = time.perf_counter() - started
        if status:
            self.close()
            raise ValueError(f"Quantized model validation returned status {status}")

    def update_stats(self, expected_live):
        self.send("stats\nmemory-size")
        self.stats = self.read("stats", 4)
        self.memory_bytes, = self.read("memory-size", 1)
        if self.stats[0] - self.stats[3] != expected_live:
            raise RuntimeError(f"Quantized session retained temporary allocations: {self.stats}")

    def step(self, token):
        position = len(self.tokens)
        if not 0 <= token < 50257 or position >= 128:
            raise ValueError("Token or position exceeds the GPT-2 context")
        self.send(f"arg-ptr 0\narg-u64 {self.weight_bytes}\narg-u64 {self.cache_pointer}\n"
                  f"arg-u64 {self.cache_size}\narg-u64 {token}\narg-u64 {position}\ncall cachedStep 5")
        status, cache, cache_size, logits, logits_size = self.read("results", 5)
        if status:
            if (cache, cache_size, logits, logits_size) != (0, 0, 0, 0):
                raise RuntimeError("A failed quantized call returned nonempty outputs")
            self.update_stats(2 if self.cache_pointer else 1)
            raise InferenceStatusError(status, position)
        if cache_size != (position + 1) * 12 * 1536 * 4 or logits_size != 50257 * 4:
            raise RuntimeError("Quantized inference returned an incorrect tensor size")
        if self.cache_pointer:
            self.release(self.cache_pointer)
        self.cache_pointer, self.cache_size = cache, cache_size
        self.tokens.append(token)
        return self.read_logits(logits, logits_size)

    def reset(self):
        if self.cache_pointer:
            self.release(self.cache_pointer)
        self.cache_pointer, self.cache_size = 0, 0
        self.tokens = []
        self.update_stats(1)

    def infer_cached(self, tokens):
        if len(tokens) <= len(self.tokens) or tokens[:len(self.tokens)] != self.tokens:
            self.reset()
        for token in tokens[len(self.tokens):]:
            logits = self.step(token)
        return logits

    def close(self):
        if self.closed:
            return
        try:
            self.reset()
            self.send("arg-ptr 0\ncall release 0")
            self.read("results", 0)
            self.update_stats(0)
            self.send("done")
            self.process.stdin.close()
            status = self.process.wait(timeout=10)
            if status:
                raise RuntimeError(f"Wasmtime session exited with status {status}")
        finally:
            self.terminate()

    def terminate(self):
        if self.process.poll() is None:
            self.process.kill()
            self.process.wait(timeout=10)
        self.process.stdin.close()
        self.process.stdout.close()
        self.closed = True

    def __exit__(self, kind, value, traceback):
        if kind is None:
            self.close()
        else:
            self.terminate()
