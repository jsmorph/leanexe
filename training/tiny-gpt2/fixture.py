import argparse
import json
from pathlib import Path
import struct

import torch

from model import TinyGpt2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    torch.manual_seed(17)
    model = TinyGpt2()
    names = ["token", "position", "query", "key", "value", "attention", "attention_bias",
             "expand", "expand_bias", "contract", "contract_bias", "head", "head_bias",
             "norm1_scale", "norm1_bias", "norm2_scale", "norm2_bias", "norm_final_scale", "norm_final_bias"]
    words = [str(struct.unpack(">Q", struct.pack(">d", x))[0])
             for name in names for x in model.weights[name].detach().reshape(-1).tolist()]
    if len(words) != 2488:
        raise ValueError("The fixture has an incorrect parameter count")
    contexts = [[97, 98, 99, 100], [97, 98, 1, 2], [0, 0, 0, 0], [255, 255, 255, 255]]
    with torch.no_grad():
        _, trace = model(torch.tensor(contexts), with_trace=True)
    cases = [{"tokens": tokens, "position": position,
              "reference": trace["norm_final"][i, position].tolist(),
              "logits": trace["logits"][i, position, [0, 32, 65, 255]].tolist()}
             for i, tokens in enumerate(contexts) for position in range(4)]
    record = {"scope": "Deterministic initialization test; no training", "seed": 17,
              "weights": words, "cases": cases}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
