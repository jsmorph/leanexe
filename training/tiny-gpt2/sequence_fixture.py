import argparse
import json
from pathlib import Path
import struct

import torch

from checkpoint import WEIGHT_NAMES, load_checkpoint
from model import TinyGpt2


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path)
    args = parser.parse_args()
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    torch.manual_seed(17)
    model = load_checkpoint(args.checkpoint)[0] if args.checkpoint else TinyGpt2(128)
    if model.context != 128:
        raise ValueError("The sequence fixture requires a 128-position model")
    weights = [str(struct.unpack(">Q", struct.pack(">d", x))[0])
               for name in WEIGHT_NAMES for x in model.weights[name].detach().reshape(-1).tolist()]
    contexts = [[97], [84, 111, 32, 98], list(range(64)), list(range(128)),
                [0] * 128, [255] * 128]
    cases = []
    with torch.no_grad():
        for tokens in contexts:
            logits = model(torch.tensor([tokens]))[0, -1].tolist()
            cases.append({"tokens": tokens, "logits": logits})
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps({"weights": weights, "cases": cases}, indent=2) + "\n")


if __name__ == "__main__":
    main()
