import numpy as np

from quantized_reference import QuantizedReference


class ExperimentReference(QuantizedReference):
    def __init__(self, reference, grouped=False, fp32_head=False):
        self.weights = reference.weights
        self.grouped = grouped
        self.head_weights = (self.weights["wte.weight"].astype(np.float32)
                             * self.weights["wte.scale"][:, None]) if fp32_head else None
        self.cache = []
        self.tokens = []

    def linear(self, values, name, bias=True):
        if not np.all(np.isfinite(values)):
            raise ValueError("Nonfinite projection input")
        if name == "wte" and self.head_weights is not None:
            result = np.zeros(50257, dtype=np.float32)
            for index, value in enumerate(values):
                result = result + self.head_weights[:, index] * value
            return result
        return super().linear(values, name, bias)

    def step(self, token):
        result = super().step(token)
        self.tokens.append(token)
        return result

    def infer(self, tokens):
        if not 1 <= len(tokens) <= 128 or any(not 0 <= token < 50257 for token in tokens):
            raise ValueError("Inference requires 1 to 128 GPT-2 token IDs")
        if len(tokens) <= len(self.tokens) or tokens[:len(self.tokens)] != self.tokens:
            self.cache = []
            self.tokens = []
        for token in tokens[len(self.tokens):]:
            logits = self.step(token)
        return logits
