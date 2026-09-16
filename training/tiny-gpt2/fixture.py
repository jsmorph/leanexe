import argparse
import json
from pathlib import Path
import struct

import torch

from model import TinyGpt2
from checkpoint import WEIGHT_NAMES, load_checkpoint


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--checkpoint", type=Path)
    args = parser.parse_args()
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    torch.manual_seed(17)
    model = load_checkpoint(args.checkpoint)[0] if args.checkpoint else TinyGpt2()
    words = [str(struct.unpack(">Q", struct.pack(">d", x))[0])
             for name in WEIGHT_NAMES for x in model.weights[name].detach().reshape(-1).tolist()]
    if len(words) != 2488:
        raise ValueError("The fixture has an incorrect parameter count")
    contexts = [[97, 98, 99, 100], [97, 98, 1, 2], [0, 0, 0, 0], [255, 255, 255, 255]]
    if args.checkpoint:
        contexts += [[0, 0, 36, 82], [84, 111, 32, 98]]
    with torch.no_grad():
        _, trace = model(torch.tensor(contexts), with_trace=True)
    cases = [{"tokens": tokens, "position": position,
              "reference": trace["norm_final"][i, position].tolist(),
              "logits": trace["logits"][i, position, [0, 32, 65, 255]].tolist()}
             for i, tokens in enumerate(contexts) for position in range(4)]
    record = {"scope": "Trained checkpoint test" if args.checkpoint else "Deterministic initialization test; no training", "seed": 17,
              "weights": words, "cases": cases}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")


if __name__ == "__main__":
    main()
