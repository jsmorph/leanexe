#!/usr/bin/env python3
"""Create a portable static browser bundle, leaving generated output ignored."""
from pathlib import Path
import sys
import zipfile

bundle = Path(sys.argv[1])
names = ['index.html', 'app.js', 'host.js', 'manifest.json', 'hidden.wasm',
         'transfer.wasm', 'finish.wasm', 'kernel.wgsl', 'weights.bin', 'reference.json']
for name in names:
    if not (bundle / name).is_file():
        raise SystemExit(f'Missing bundle file: {name}')
readme = '''GPT2/128 local Wasm + WebGPU demo

Extract this archive, then run in that directory:
  python3 -m http.server 8765 --bind 127.0.0.1
Open http://localhost:8765/ in a WebGPU-capable browser.
Alternatively, serve these files unchanged from an HTTPS static website.

Inference runs locally in Wasm and WGSL. JavaScript only handles browser APIs,
byte transfers, and UI controls. No model server, Lean installation or build
step is needed to use the browser bundle. Every generation step runs the model.

This checkpoint is a 2,984-parameter test model with poor language quality.
The full transformer Wasm and transfer-adapter proofs are incomplete.
See manifest.json for artifact identities; browser WebGPU arithmetic can differ
from the restricted exact profile. The comparison panel reports those differences.
'''
with zipfile.ZipFile(bundle / 'browser.zip', 'w', zipfile.ZIP_DEFLATED) as archive:
    for name in names:
        archive.write(bundle / name, name)
    archive.writestr('README.txt', readme)
print(bundle / 'browser.zip')
