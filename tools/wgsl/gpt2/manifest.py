#!/usr/bin/env python3
"""Bind this local bundle and native build to exact artifact bytes."""
from pathlib import Path
import hashlib
import json
import sys
out = Path(sys.argv[1])
manifest = json.loads((out/'layout.json').read_text())
entry = manifest.get('shaderEntryPoint', 'gemm_f32')
if entry not in ('gemm_f32', 'lean_kernel'):
    raise ValueError('unsupported WGSL entry point')
names = ['model.wasm','tokenizer.wasm','transfer.wasm','embedding.bin','params.bin','tokenizer.bin']
names += [s['shader'] for s in manifest['shapes']]+[m['file'] for m in manifest['matrices']]
manifest['sha256'] = {n:hashlib.file_digest((out/n).open('rb'),'sha256').hexdigest() for n in names}
manifest['sizes'] = {n:(out/n).stat().st_size for n in names}
(out/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
(out/'artifacts.h').write_text(f'#define ARTIFACT_COUNT {len(names)}\n#define WGSL_ENTRY_POINT {json.dumps(entry)}\n'+
    'static const char *artifact_names[] = {'+','.join(json.dumps(n) for n in names)+'};\n'+
    'static const char *artifact_hashes[] = {'+','.join(json.dumps(manifest['sha256'][n]) for n in names)+'};\n'+
    'static const size_t artifact_sizes[] = {'+','.join(str(manifest['sizes'][n]) for n in names)+'};\n')
