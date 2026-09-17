import argparse
import hashlib
import json
import math
from pathlib import Path
import struct

import torch

from model import TinyGpt2


def word(x):
    if not math.isfinite(x):
        raise ValueError("A checkpoint value is nonfinite")
    return struct.pack(">d", x).hex().upper()


def windows(data, context):
    return torch.tensor(list(data), dtype=torch.long).unfold(0, context + 1, 1)


def loss_on(model, data, limit=8192):
    selected = data[torch.linspace(0, len(data) - 1, min(limit, len(data))).long()]
    total = 0.0
    with torch.no_grad():
        for batch in selected.split(256):
            logits = model(batch[:, :-1])
            loss = torch.nn.functional.cross_entropy(logits.reshape(-1, 256), batch[:, 1:].reshape(-1))
            total += float(loss) * len(batch)
    return total / len(selected)


def audit_ranges(model, data):
    result = {}
    selected = data[torch.linspace(0, len(data) - 1, min(16384, len(data))).long(), :-1]
    single_bytes = torch.arange(256).unsqueeze(1).expand(-1, model.context)
    generator = torch.Generator().manual_seed(1729)
    arbitrary = torch.randint(256, (16384, model.context), generator=generator)
    with torch.no_grad():
        for batch in torch.cat([selected, single_bytes, arbitrary]).split(256):
            _, trace = model(batch, with_trace=True)
            for name, values in trace.items():
                low, high = float(values.min()), float(values.max())
                old = result.setdefault(name, {"min": low, "max": high})
                old["min"] = min(old["min"], low)
                old["max"] = max(old["max"], high)
    return {"scope": "Sampled corpus windows, all constant-byte windows, and 16384 seeded byte windows",
            "formal_certificate": False, "ranges": result}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--corpus", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--steps", type=int, default=4000)
    parser.add_argument("--seed", type=int, default=17)
    parser.add_argument("--batch-size", type=int, default=128)
    parser.add_argument("--learning-rate", type=float, default=0.001)
    parser.add_argument("--context", type=int, choices=(4, 64, 128), default=4)
    args = parser.parse_args()
    if args.steps < 1 or args.batch_size < 1 or not 0 < args.learning_rate < 1:
        parser.error("Steps and batch size must be positive, and learning rate must lie in (0, 1)")
    if torch.__version__ != "2.9.1+cpu":
        raise ValueError(f"Expected torch 2.9.1+cpu, received {torch.__version__}")
    torch.set_num_threads(1)
    torch.set_num_interop_threads(1)
    torch.set_default_dtype(torch.float64)
    torch.use_deterministic_algorithms(True)
    torch.manual_seed(args.seed)
    corpus = args.corpus.read_bytes()
    split = len(corpus) * 9 // 10
    if split <= args.context or len(corpus) - split <= args.context:
        raise ValueError("Both corpus splits must contain a full context and its next byte")
    training, validation = windows(corpus[:split], args.context), windows(corpus[split:], args.context)
    model = TinyGpt2(args.context)
    optimizer = torch.optim.Adam(model.parameters(), lr=args.learning_rate)
    before = {"training": loss_on(model, training), "validation": loss_on(model, validation)}
    print(json.dumps({"step": 0, "loss": before}), flush=True)
    for step in range(1, args.steps + 1):
        batch = training[torch.randint(len(training), (args.batch_size,))]
        logits = model(batch[:, :-1])
        loss = torch.nn.functional.cross_entropy(logits.reshape(-1, 256), batch[:, 1:].reshape(-1))
        if not torch.isfinite(loss):
            raise ValueError(f"Training loss became nonfinite at step {step}")
        optimizer.zero_grad(set_to_none=True)
        loss.backward()
        optimizer.step()
        if step % 500 == 0 or step == args.steps:
            print(json.dumps({"step": step, "batch_loss": float(loss.detach())}), flush=True)
    after = {"training": loss_on(model, training), "validation": loss_on(model, validation)}
    weights = {}
    for name, parameter in model.weights.items():
        weights[name] = {"shape": list(parameter.shape),
                         "bits": [word(x) for x in parameter.detach().reshape(-1).tolist()]}
    record = {
        "format": "leanexe-tiny-gpt2-checkpoint-v1",
        "architecture": {"context": args.context, "vocabulary": 256, "width": 4, "heads": 2,
                         "head_width": 2, "feedforward_width": 8, "blocks": 1,
                         "activation": "tanh-gelu", "epsilon": "1/100000",
                         "pre_normalized": True, "qkv_bias": False,
                         "attention_output_bias": True, "head_tied": False,
                         "matrix_layout": "input-by-output, row-major"},
        "training": {"torch": torch.__version__, "dtype": "float64", "seed": args.seed,
                     "steps": args.steps, "batch_size": args.batch_size,
                     "learning_rate": args.learning_rate, "optimizer": "Adam",
                     "corpus_sha256": hashlib.sha256(corpus).hexdigest(),
                     "corpus_bytes": len(corpus), "training_bytes": split,
                     "loss_before": before, "loss_after": after},
        "range_audit": audit_ranges(model, training), "weights": weights,
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({"loss_after": after, "output": str(args.output)}), flush=True)


if __name__ == "__main__":
    main()
