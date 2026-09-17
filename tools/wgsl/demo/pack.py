#!/usr/bin/env python3
"""Package existing checkpoint/artifact bytes. No inference or model arithmetic."""
import hashlib
import json
from pathlib import Path
import shutil
import struct
import sys

root, output = map(Path, sys.argv[1:])
checkpoint_path = root / 'data/tiny-gpt2-128-v1/checkpoint.json'
checkpoint = json.loads(checkpoint_path.read_text())
names = ['token', 'position', 'query', 'key', 'value', 'attention', 'attention_bias',
         'expand', 'expand_bias', 'contract', 'contract_bias', 'head', 'head_bias',
         'norm1_scale', 'norm1_bias', 'norm2_scale', 'norm2_bias', 'norm_final_scale', 'norm_final_bias']
words = [int(word, 16) for name in names for word in checkpoint['weights'][name]['bits']]
assert len(words) == 2984
assert checkpoint['architecture']['context'] == 128
(output / 'weights.bin').write_bytes(b''.join(struct.pack('<Q', w) for w in words))
for name in ('finish.wasm', 'kernel.wgsl'):
    shutil.copyfile(root / 'test/wgsl/gpt' / name, output / name)
references = []
for path in sorted((root / 'test/wgsl/gpt128/reference').glob('*.json')):
    data = json.loads(path.read_text())
    references.append({'name': path.stem, **{key: data[key] for key in
        ('tokens', 'preparedWeights', 'hidden', 'a', 'b', 'headWords', 'logits')}})
(output / 'reference.json').write_text(json.dumps(references, separators=(',', ':')) + '\n')
files = ['hidden.wasm', 'transfer.wasm', 'finish.wasm', 'kernel.wgsl', 'weights.bin', 'reference.json']
manifest = {'schemaVersion': 1, 'model': 'GPT2/128', 'contextBytes': 128,
            'parameters': 2984, 'decoding': 'greedy; lowest byte wins ties; sliding last 128 bytes',
            'hiddenArtifactProofComplete': False, 'transferArtifactProofComplete': False,
            'runtimeConformanceEstablished': False,
            'checkpointSha256': hashlib.sha256(checkpoint_path.read_bytes()).hexdigest(),
            'sha256': {name: hashlib.sha256((output / name).read_bytes()).hexdigest() for name in files}}
(output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
(output / 'artifacts.h').write_text('static const char *artifact_names[] = {' +
    ','.join(json.dumps(x) for x in files[:5]) + '};\nstatic const char *artifact_hashes[] = {' +
    ','.join(json.dumps(manifest['sha256'][x]) for x in files[:5]) + '};\n')
print(f'Packaged {len(words)} weights and generated artifacts in {output}')
