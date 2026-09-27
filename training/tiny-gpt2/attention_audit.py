import argparse
import json
import math
from pathlib import Path

import torch

from checkpoint import load_checkpoint


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    torch.set_num_threads(1)
    torch.set_default_dtype(torch.float64)
    model, _ = load_checkpoint(args.checkpoint)
    results = []
    with torch.no_grad():
        tokens = torch.arange(256).unsqueeze(1).expand(-1, 4)
        _, trace = model(tokens, with_trace=True)
        query, key = trace["query"], trace["key"]
        for position in range(1, 4):
            for head in range(2):
                scores = torch.einsum("qd,tjd->qtj", query[:, head, position],
                                      key[:, head, :position+1]) / math.sqrt(2)
                lower, lower_token = scores.min(1)
                upper, upper_token = scores.max(1)
                diagonal = scores[torch.arange(256), torch.arange(256), position]
                lower[:, position] = diagonal
                upper[:, position] = diagonal
                lower_token[:, position] = torch.arange(256)
                upper_token[:, position] = torch.arange(256)
                best = None
                for high_position in range(position+1):
                    for low_position in range(position+1):
                        if high_position == low_position:
                            continue
                        spread, query_token = (upper[:, high_position] - lower[:, low_position]).max(0)
                        if best is None or float(spread) > best["spread"]:
                            context = [0, 0, 0, 0]
                            context[position] = int(query_token)
                            context[high_position] = int(upper_token[query_token, high_position])
                            context[low_position] = int(lower_token[query_token, low_position])
                            best = {"position": position, "head": head, "spread": float(spread),
                                    "tokens": context}
                _, witness = model(torch.tensor([best["tokens"]]), with_trace=True)
                active = witness["scores"][0, head, position, :position+1]
                measured = float(active.max() - active.min())
                if abs(measured - best["spread"]) > 1e-12:
                    raise ValueError("Attention spread witness does not match the enumeration")
                best["scores"] = active.tolist()
                results.append(best)
    record = {"scope": "CPU binary64 enumeration of token pairs at distinct active key positions",
              "formal_certificate": False, "results": results}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps(record), flush=True)


if __name__ == "__main__":
    main()
