import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys
import time
import urllib.request


ROOT = Path(__file__).resolve().parents[2]
MANIFEST = json.loads((ROOT / "data/gpt2-124m/manifest.json").read_text())


def digest(path):
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def check_files(directory):
    for name, expected in MANIFEST["files"].items():
        if digest(directory / name) != expected:
            raise ValueError(f"{name}: SHA-256 differs from the pinned checkpoint")


def fetch(directory):
    directory.mkdir(parents=True, exist_ok=True)
    for name, expected in MANIFEST["files"].items():
        destination = directory / name
        if destination.exists() and digest(destination) == expected:
            continue
        url = f'https://huggingface.co/{MANIFEST["model"]}/resolve/{MANIFEST["revision"]}/{name}'
        partial = destination.with_suffix(destination.suffix + ".part")
        with urllib.request.urlopen(url, timeout=120) as response, partial.open("wb") as output:
            shutil.copyfileobj(response, output)
        if digest(partial) != expected:
            raise ValueError(f"{name}: downloaded SHA-256 differs from the pinned checkpoint")
        partial.replace(destination)
        print(f"Downloaded {name}", file=sys.stderr)
    check_files(directory)


def generate(args):
    import torch
    import transformers

    torch.set_num_threads(1)
    check_files(args.model_dir)
    tokenizer = transformers.AutoTokenizer.from_pretrained(args.model_dir, local_files_only=True)
    model = transformers.GPT2LMHeadModel.from_pretrained(
        args.model_dir, local_files_only=True, dtype=torch.float32, attn_implementation="eager").eval()
    parameter_count = sum(p.numel() for p in model.parameters())
    if parameter_count != MANIFEST["parameters"]:
        raise ValueError(f"Expected {MANIFEST['parameters']} parameters, got {parameter_count}")
    inputs = tokenizer(args.text, return_tensors="pt")
    prompt_tokens = inputs.input_ids[0].tolist()
    limit = MANIFEST["reference_context_limit"]
    if not 1 <= len(prompt_tokens) < limit:
        raise ValueError(f"Generation requires a prompt of 1 to {limit - 1} GPT-2 tokens")
    count = min(args.max_new_tokens, limit - len(prompt_tokens))
    sampling = {"do_sample": args.top_k > 1}
    if args.top_k > 1:
        sampling.update(top_k=args.top_k, temperature=args.temperature)
    started = time.monotonic()
    torch.manual_seed(args.seed)
    with torch.inference_mode():
        output = model.generate(**inputs, max_new_tokens=count, **sampling,
                                pad_token_id=tokenizer.eos_token_id)
    generated = output[0].tolist()[len(prompt_tokens):]
    return {
        "runtime": "Transformers CPU PyTorch FP32",
        "model": MANIFEST["model"], "revision": MANIFEST["revision"],
        "checkpoint_sha256": MANIFEST["files"]["model.safetensors"],
        "parameters": parameter_count, "context_limit": limit,
        "torch": torch.__version__, "transformers": transformers.__version__,
        "seed": args.seed, "top_k": args.top_k, "temperature": args.temperature,
        "prompt": args.text, "prompt_tokens": prompt_tokens, "generated_tokens": generated,
        "completion": tokenizer.decode(generated, skip_special_tokens=True),
        "text": tokenizer.decode(output[0], skip_special_tokens=True),
        "stop_reason": "eos" if generated[-1] == tokenizer.eos_token_id else
            ("context_limit" if len(prompt_tokens) + len(generated) == limit else "length"),
        "seconds": time.monotonic() - started,
    }


def main():
    parser = argparse.ArgumentParser(description="Run the pinned pretrained GPT-2 124M CPU reference")
    parser.add_argument("command", choices=["fetch", "generate"])
    parser.add_argument("--model-dir", type=Path, default=ROOT / "build/gpt2-124m")
    parser.add_argument("--text")
    parser.add_argument("--max-new-tokens", type=int, default=64)
    parser.add_argument("--seed", type=int, default=42)
    parser.add_argument("--top-k", type=int, default=40)
    parser.add_argument("--temperature", type=float, default=0.8)
    parser.add_argument("--json", action="store_true")
    args = parser.parse_args()
    if args.command == "fetch":
        fetch(args.model_dir)
        print("Checked the pinned GPT-2 checkpoint and tokenizer")
        return
    if args.text is None:
        parser.error("generate requires --text")
    if args.max_new_tokens <= 0:
        parser.error("--max-new-tokens must be positive")
    if not 1 <= args.top_k <= MANIFEST["vocabulary"]:
        parser.error("--top-k is outside the vocabulary")
    if not 0 < args.temperature < float("inf"):
        parser.error("--temperature must be positive and finite")
    if not 0 <= args.seed < 2**64:
        parser.error("--seed must be a UInt64 integer")
    result = generate(args)
    print(json.dumps(result) if args.json else result["text"])


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, RuntimeError) as error:
        print(f"gpt2-reference: {error}", file=sys.stderr)
        sys.exit(1)
