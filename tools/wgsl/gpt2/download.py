#!/usr/bin/env python3
"""Fetch the pinned public GPT-2 checkpoint and tokenizer; never execute model code."""
from pathlib import Path
import hashlib
import json
import sys
import urllib.request

REVISION = '607a30d783dfa663caf39e06633721c8d4cfcd7e'
BASE = f'https://huggingface.co/openai-community/gpt2/resolve/{REVISION}/'
NAMES = ['config.json', 'model.safetensors', 'vocab.json', 'merges.txt', 'tokenizer.json', 'tokenizer_config.json', 'README.md']
HASHES = [
    '0daed7749b4f02b8f76240d5444551d7b08712dab4d0adb8239c56ba823bb7b4',
    '248dfc3911869ec493c76e65bf2fcf7f615828b0254c12b473182f0f81d3a707',
    '196139668be63f3b5d6574427317ae82f612a97c5d1cdaf36ed2256dbf636783',
    '1ce1664773c50f3e0cc8842619a93edc4624525b728b188a9e0be33b7726adc5',
    '8414cab924d8b9b33013f0d221c5862f365ee9be39c5c2bfae8a5a9e970478a6',
    '5e04eb606e3a1583530a42e36c2a6b6615c86f34fe77e44d9ddeb43ff940931f',
    '0fcd631078093c2aa1d93438b898320b8a1167784e2a1ab37b8016e9de8b3c2e',
]
out = Path(sys.argv[1]); out.mkdir(parents=True, exist_ok=True)
for name, expected in zip(NAMES,HASHES):
    dest = out / name
    if not dest.exists():
        partial = dest.with_suffix(dest.suffix + '.partial')
        print(f'Downloading {name}', flush=True)
        with urllib.request.urlopen(BASE + name, timeout=60) as response, partial.open('wb') as f:
            while chunk := response.read(1024*1024):
                f.write(chunk)
        partial.rename(dest)
    digest = hashlib.file_digest(dest.open('rb'), 'sha256').hexdigest()
    if digest != expected:
        raise ValueError(f'{name}: SHA-256 differs from the pinned source')
    print(name, dest.stat().st_size, digest, flush=True)
(out / 'source.json').write_text(json.dumps({'repository': 'openai-community/gpt2', 'revision': REVISION,
    'sha256': {name: hashlib.file_digest((out/name).open('rb'),'sha256').hexdigest() for name in NAMES}}, indent=2)+'\n')
