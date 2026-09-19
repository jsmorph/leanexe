#!/usr/bin/env python3
"""Offline packing only. Runtime computation remains in Wasm and WGSL."""
import hashlib
import json
from pathlib import Path
import sys

import numpy as np
from safetensors.numpy import load_file
from tokenizer_table import pack_tokenizer

source, destination = map(Path, sys.argv[1:3])
destination.mkdir(parents=True, exist_ok=True)
checkpoint = source / "model.safetensors"
assert hashlib.file_digest(checkpoint.open("rb"), "sha256").hexdigest() == \
    "248dfc3911869ec493c76e65bf2fcf7f615828b0254c12b473182f0f81d3a707"
weights = load_file(checkpoint)
block_names = ["ln_1.weight", "ln_1.bias", "attn.c_attn.weight", "attn.c_attn.bias",
               "attn.c_proj.weight", "attn.c_proj.bias", "ln_2.weight", "ln_2.bias",
               "mlp.c_fc.weight", "mlp.c_fc.bias", "mlp.c_proj.weight", "mlp.c_proj.bias"]
names = ["wte.weight", "wpe.weight"] + [f"h.{i}.{name}" for i in range(12) for name in block_names] + ["ln_f.weight", "ln_f.bias"]
file = destination / "weights.bin"
with file.open("xb") as stream:
    for name in names:
        value = weights[name]
        assert value.dtype == np.float32 and np.isfinite(value).all(), name
        stream.write(value.astype("<f4", copy=False).tobytes())
digest = hashlib.file_digest(file.open("rb"), "sha256").hexdigest()
assert file.stat().st_size == 497759232 and digest == "6c12f993878ad39ba4aa3b0ab58a7466f5a62651cda94464dab438339008ba1d"
table_words, unicode_version = pack_tokenizer(source, destination)
(destination / "assets.json").write_text(json.dumps({"weightsSha256": digest, "tokenizerWords": table_words,
    "unicodeVersion": unicode_version, "source": json.loads((source / "source.json").read_text())}, indent=2)+"\n")
print(f"Packed 124,439,808 FP32 weights and {table_words} tokenizer words.")
