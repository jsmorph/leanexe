#!/usr/bin/env python3
"""Small regression for rebuilt tokenizer/sampler and native request limits."""
import json
import os
from pathlib import Path
import subprocess
import sys
from transformers import AutoTokenizer

root = Path(__file__).resolve().parents[3]
bundle, output = map(lambda p: Path(p).resolve(), sys.argv[1:3])
output.mkdir()
texts = ["Hello, world!", "don't stop, we're here.", "  spaces\n\tlines\n", "café naïve résumé",
         "你好世界 🌍", "αβγ Δ", "a\u0301", "The purpose of science is"]
request, actual = output / "input.json", output / "wasm.json"
request.write_text(json.dumps({"texts": texts}))
subprocess.run(["node", str(root / "tools/wgsl/gpt2/packed-aux-call.mjs"), str(bundle), str(request), str(actual)], check=True, timeout=90)
result = json.loads(actual.read_text())
tokenizer = AutoTokenizer.from_pretrained(root / "build/gpt2/source", local_files_only=True)
for row in result["cases"]:
    assert row["tokens"] == tokenizer.encode(row["text"], add_special_tokens=False), row
    assert bytes(row["decoded"]) == row["text"].encode("utf-8"), row
assert len(result["eos"]) == 2 and result["eos"][0] == "50256", result["eos"]
invalid = [(["--prompt", ""], "prompt"), (["--prompt", " a"*127, "--generate", "2"], "128 tokens"),
           (["--prompt", "hello", "--seed", "0"], "seed"), (["--prompt", "hello", "--temperature", "-1"], "temperature")]
for args, message in invalid:
    process = subprocess.run([str(root / "tools/gpt2-packed"), *args], capture_output=True, text=True, timeout=30,
                             env=dict(os.environ, LEANEXE_GPT2_PACKED_BUNDLE=str(bundle)))
    assert process.returncode != 0 and message in process.stderr, (args, process.stderr)
(output / "results.json").write_text(json.dumps({"status": "pass", "tokenizerCases": len(texts),
    "utf8RoundTripsExact": True, "greedyEosFixture": "50256", "invalidRequestsRejected": len(invalid)}, indent=2)+"\n")
print("PASS: eight tokenizer/reference comparisons and UTF-8 round trips, Wasm EOS selection, four invalid requests")
