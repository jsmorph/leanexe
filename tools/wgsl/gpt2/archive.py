#!/usr/bin/env python3
"""Package a portable browser bundle, leaving every generated file under build/."""
from pathlib import Path
import json
import sys
import zipfile
out = Path(sys.argv[1])
manifest = json.loads((out/'manifest.json').read_text())
names = list(manifest['sha256'])+['manifest.json','index.html','app.js','host.js']
archive = out.parent/'gpt2-browser.zip'
with zipfile.ZipFile(archive,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=1) as z:
    for name in names:
        z.write(out/name,'gpt2-browser/'+name)
    z.writestr('gpt2-browser/README.txt',
        'Pretrained GPT-2: Lean-generated Wasm + generated WGSL\n\n'
        'Extract this folder and serve it on localhost or HTTPS. For example:\n'
        '  python3 -m http.server 8766 --bind 127.0.0.1\n'
        'Then open http://localhost:8766/ in a WebGPU-enabled browser.\n'
        'The HTTP server only serves files; all inference happens in the browser.\n'
        'Model arithmetic and tokenization run in Wasm/WGSL; JavaScript is host bindings.\n'
        'This demo has incomplete formal proofs and a 128-token total context limit.\n'
        'Checkpoint: openai-community/gpt2, revision '+manifest['source']['revision']+'\n'
        'Each model artifact is checked against the included SHA-256 manifest.\n')
print(f'{archive}: {archive.stat().st_size} bytes')
