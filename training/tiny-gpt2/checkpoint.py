import json
import math
import struct

import torch

from model import TinyGpt2


WEIGHT_NAMES = ["token", "position", "query", "key", "value", "attention", "attention_bias",
                "expand", "expand_bias", "contract", "contract_bias", "head", "head_bias",
                "norm1_scale", "norm1_bias", "norm2_scale", "norm2_bias", "norm_final_scale", "norm_final_bias"]


def load_checkpoint(path):
    record = json.loads(path.read_text())
    if record["format"] != "leanexe-tiny-gpt2-checkpoint-v1":
        raise ValueError("Unsupported checkpoint format")
    model = TinyGpt2(record["architecture"]["context"])
    if set(record["weights"]) != set(model.weights):
        raise ValueError("Checkpoint tensor names differ from the model")
    with torch.no_grad():
        for name, parameter in model.weights.items():
            tensor = record["weights"][name]
            if tensor["shape"] != list(parameter.shape) or len(tensor["bits"]) != parameter.numel():
                raise ValueError(f"Invalid checkpoint shape: {name}")
            values = [struct.unpack(">d", bytes.fromhex(word))[0] for word in tensor["bits"]]
            if not all(math.isfinite(value) for value in values):
                raise ValueError(f"Nonfinite checkpoint value: {name}")
            parameter.copy_(torch.tensor(values).reshape(parameter.shape))
    return model, record
