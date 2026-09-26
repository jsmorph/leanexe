import hashlib
import json

import numpy as np

from quantized import GROUPED_HEADER, HEADER, MODEL_BYTES, model_layout


F32 = np.float32


def word(value):
    return np.array(value, dtype=np.uint32).view(np.float32)[()]


def sum_serial(values):
    total = np.zeros(values.shape[1:], dtype=np.float32)
    for value in values:
        total = total + value
    return total


def exp_negative(values):
    cutoff = values.view(np.uint32) > 0xC2800000
    reduced = np.where(cutoff, F32(0), values)
    squares = np.zeros(values.shape, dtype=np.uint32)
    for _ in range(6):
        halve = reduced.view(np.uint32) > 0xBF800000
        reduced = np.where(halve, reduced * F32(0.5), reduced)
        squares += halve
    coefficients = [
        0x253413C3, 0x274A963C, 0x29573F9F, 0x2B573F9F, 0x2D49CBA5,
        0x2F309231, 0x310F76C7, 0x32D7322B, 0x3493F27E, 0x3638EF1D,
        0x37D00D01, 0x39500D01, 0x3AB60B61, 0x3C088889, 0x3D2AAAAB,
        0x3E2AAAAB, 0x3F000000, 0x3F800000, 0x3F800000,
    ]
    result = np.full(values.shape, word(coefficients[0]), dtype=np.float32)
    for coefficient in coefficients[1:]:
        result = result * reduced + word(coefficient)
    for index in range(6):
        result = np.where(index < squares, result * result, result)
    return np.where(cutoff, F32(0), result)


def gelu(values):
    magnitude = np.abs(values)
    bounded = np.minimum(magnitude, F32(8))
    square = bounded * bounded
    factor = square * word(0x3D372713) + F32(1)
    exponent = (factor * bounded) * word(0x3FCC422A)
    exponential = exp_negative(-exponent)
    denominator = F32(1) + exponential
    result = np.where(np.signbit(values), (-bounded * exponential) / denominator,
                      bounded / denominator)
    return np.where(magnitude > F32(8), np.where(np.signbit(values), F32(0), values), result)


class QuantizedReference:
    def __init__(self, directory, grouped=False):
        data = (directory / "weights.bin").read_bytes()
        manifest = json.loads((directory / "manifest.json").read_text())
        if len(data) != MODEL_BYTES or data[:len(HEADER)] != (GROUPED_HEADER if grouped else HEADER):
            raise ValueError("Invalid quantized model header or length")
        if hashlib.sha256(data).hexdigest() != manifest["weights_sha256"]:
            raise ValueError("Quantized model digest mismatch")
        self.grouped = grouped
        self.weights = {}
        for record in model_layout():
            name, shape = record["name"], record["shape"]
            dtype = np.int8 if record["dtype"] == "i8" else np.dtype("<f4")
            value = np.frombuffer(data, dtype=dtype, count=np.prod(shape),
                                  offset=record["offset_bytes"]).reshape(shape)
            if record["dtype"] == "i8":
                if np.any(value == -128):
                    raise ValueError(f"Reserved coefficient in {name}")
                value = value.astype(np.int32)
            elif not np.all(np.isfinite(value)):
                raise ValueError(f"Nonfinite parameter in {name}")
            elif name.endswith(".scale") and np.any(value < word(0x00800000)):
                raise ValueError(f"Invalid scale in {name}")
            self.weights[name] = value
        self.cache = []

    def normalize(self, values, name):
        mean = sum_serial(values) / F32(768)
        centered = values - mean
        variance = sum_serial(centered * centered) / F32(768)
        inverse = F32(1) / np.sqrt(variance + word(0x3727C5AC))
        return ((centered * inverse) * self.weights[name + ".weight"]
                + self.weights[name + ".bias"])

    def linear(self, values, name, bias=True):
        if not np.all(np.isfinite(values)):
            raise ValueError("Nonfinite projection input")
        if self.grouped:
            if len(values) % 64:
                raise ValueError("Grouped projection requires a multiple of 64 inputs")
            matrix = self.weights[name + ".weight"]
            scales = self.weights[name + ".scale"]
            result = np.zeros(matrix.shape[0], dtype=np.float32)
            for start in range(0, len(values), 64):
                group = values[start:start + 64]
                maximum = np.max(np.abs(group))
                scale = F32(1) if maximum == 0 else np.maximum(maximum / F32(127), word(0x00800000))
                codes = np.rint(np.clip(group / scale, F32(-127), F32(127))).astype(np.int32)
                accumulator = matrix[:, start:start + 64] @ codes
                if np.max(np.abs(accumulator)) > 64 * 16129:
                    raise ValueError("Grouped accumulator exceeds its specified range")
                result = result + accumulator.astype(np.float32) * (scale * scales)
            return result + self.weights[name + ".bias"] if bias else result
        maximum = np.max(np.abs(values))
        scale = F32(1) if maximum == 0 else np.maximum(maximum / F32(127), word(0x00800000))
        quantized = np.rint(np.clip(values / scale, F32(-127), F32(127))).astype(np.int32)
        accumulator = self.weights[name + ".weight"] @ quantized
        if np.max(np.abs(accumulator)) > len(values) * 16129:
            raise ValueError("Accumulator exceeds its specified range")
        result = accumulator.astype(np.float32) * (scale * self.weights[name + ".scale"])
        return result + self.weights[name + ".bias"] if bias else result

    def attention(self, qkv, layer):
        history = np.stack([item[layer] for item in self.cache] + [qkv[768:]])
        keys = history[:, :768].reshape(-1, 12, 64)
        values = history[:, 768:].reshape(-1, 12, 64)
        query = qkv[:768].reshape(12, 64)
        scores = np.zeros(keys.shape[:2], dtype=np.float32)
        for channel in range(64):
            scores = scores + keys[:, :, channel] * query[:, channel]
        scores = scores * F32(0.125)
        exponentials = exp_negative(scores - np.max(scores, axis=0))
        probabilities = exponentials / sum_serial(exponentials)
        return sum_serial(probabilities[:, :, None] * values).reshape(768)

    def step(self, token):
        position = len(self.cache)
        if not 0 <= token < 50257 or position >= 128:
            raise ValueError("Token or position exceeds the GPT-2 context")
        hidden = (self.weights["wte.weight"][token].astype(np.float32)
                  * self.weights["wte.scale"][token]) + self.weights["wpe.weight"][position]
        updates = []
        for layer in range(12):
            prefix = f"h.{layer}."
            normalized = self.normalize(hidden, prefix + "ln_1")
            qkv = self.linear(normalized, prefix + "attn.c_attn")
            mixed = self.attention(qkv, layer)
            residual = hidden + self.linear(mixed, prefix + "attn.c_proj")
            normalized = self.normalize(residual, prefix + "ln_2")
            expanded = self.linear(normalized, prefix + "mlp.c_fc")
            hidden = residual + self.linear(gelu(expanded), prefix + "mlp.c_proj")
            updates.append(qkv[768:])
        logits = self.linear(self.normalize(hidden, "ln_f"), "wte", bias=False)
        updates = np.stack(updates)
        if not np.all(np.isfinite(logits)) or not np.all(np.isfinite(updates)):
            raise ValueError("Nonfinite inference output")
        self.cache.append(updates)
        return logits

    def cache_bytes(self):
        return np.stack(self.cache).astype("<f4").tobytes() if self.cache else b""
