import math

import torch
from torch import nn


class TinyGpt2(nn.Module):
    def __init__(self, context=4):
        super().__init__()
        if context not in (4, 64):
            raise ValueError("Context must be 4 or 64")
        self.context = context
        self.weights = nn.ParameterDict()
        for name, rows, columns in [
            ("token", 256, 4), ("position", context, 4),
            ("query", 4, 4), ("key", 4, 4), ("value", 4, 4),
            ("attention", 4, 4), ("expand", 4, 8), ("contract", 8, 4),
            ("head", 4, 256),
        ]:
            bound = 0.02 if name in ("token", "position") else math.sqrt(6 / (rows + columns))
            self.weights[name] = nn.Parameter(torch.empty(rows, columns).uniform_(-bound, bound))
        for name, width in [("attention", 4), ("expand", 8), ("contract", 4), ("head", 256)]:
            self.weights[name + "_bias"] = nn.Parameter(torch.zeros(width))
        for name in ("norm1", "norm2", "norm_final"):
            self.weights[name + "_scale"] = nn.Parameter(torch.ones(4))
            self.weights[name + "_bias"] = nn.Parameter(torch.zeros(4))

    def norm(self, x, name, trace):
        mean = ((x[..., 0] + x[..., 1]) + (x[..., 2] + x[..., 3])) / 4
        centered = x - mean.unsqueeze(-1)
        squares = centered * centered
        variance = ((squares[..., 0] + squares[..., 1]) + (squares[..., 2] + squares[..., 3])) / 4
        normalized = centered / torch.sqrt(variance.unsqueeze(-1) + 1e-5)
        result = normalized * self.weights[name + "_scale"] + self.weights[name + "_bias"]
        trace[name + "_variance"] = variance
        trace[name] = result
        return result

    def affine(self, x, name):
        return x @ self.weights[name] + self.weights[name + "_bias"]

    def forward(self, tokens, with_trace=False):
        batch, length = tokens.shape
        if not 1 <= length <= self.context:
            raise ValueError(f"The model requires 1 to {self.context} byte tokens")
        trace = {}
        x = self.weights["token"][tokens] + self.weights["position"][:length]
        trace["embedding"] = x
        normalized = self.norm(x, "norm1", trace)
        projections = []
        for name in ("query", "key", "value"):
            projected = (normalized @ self.weights[name]).reshape(batch, length, 2, 2).transpose(1, 2)
            projections.append(projected)
            trace[name] = projected
        query, key, value = projections
        scores = (query @ key.transpose(-1, -2)) / math.sqrt(2)
        trace["scores"] = scores
        mask = torch.ones(length, length, dtype=torch.bool).triu(1)
        probability = torch.softmax(scores.masked_fill(mask, -torch.inf), dim=-1)
        attended = (probability @ value).transpose(1, 2).reshape(batch, length, 4)
        trace["attended"] = attended
        x = x + self.affine(attended, "attention")
        trace["residual1"] = x
        expanded = self.affine(self.norm(x, "norm2", trace), "expand")
        trace["gelu_input"] = expanded
        activated = torch.nn.functional.gelu(expanded, approximate="tanh")
        trace["gelu_output"] = activated
        x = x + self.affine(activated, "contract")
        trace["residual2"] = x
        logits = self.affine(self.norm(x, "norm_final", trace), "head")
        trace["logits"] = logits
        return (logits, trace) if with_trace else logits
