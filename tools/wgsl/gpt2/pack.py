#!/usr/bin/env python3
"""Offline checkpoint/table packing. No Python is used by inference."""
from pathlib import Path
import hashlib
import json
import sys
from tokenizer_table import pack_tokenizer
import numpy as np
from safetensors.numpy import load_file

source, out = map(Path, sys.argv[1:3])
out.mkdir(parents=True, exist_ok=True)
expected = '248dfc3911869ec493c76e65bf2fcf7f615828b0254c12b473182f0f81d3a707'
assert hashlib.file_digest((source/'model.safetensors').open('rb'), 'sha256').hexdigest() == expected
weights = load_file(source/'model.safetensors')

def tensor(name, shape):
    a = weights[name]
    assert a.shape == shape and a.dtype == np.float32 and np.isfinite(a).all(), name
    return a

embedding = tensor('wte.weight', (50257,768))
with (out/'embedding.bin').open('wb') as f:
    f.write(embedding.astype('<f4').tobytes())
    f.write(tensor('wpe.weight',(1024,768))[:128].astype('<f4').tobytes())

shapes = [(768,2304),(768,768),(768,3072),(3072,768),(768,25129),(768,25128)]
matrices, parameters, offsets = [], [], []
for layer in range(12):
    prefix = f'h.{layer}.'
    for name, shape_id in [('attn.c_attn',0),('attn.c_proj',1),('mlp.c_fc',2),('mlp.c_proj',3)]:
        filename = f'matrix-{len(matrices):02}.bin'
        tensor(prefix+name+'.weight',shapes[shape_id]).astype('<f4').tofile(out/filename)
        matrices.append({'file':filename,'shape':shape_id})
    offsets.append(sum(a.size for a in parameters))
    for name, size in [('ln_1.weight',768),('ln_1.bias',768),('attn.c_attn.bias',2304),
                       ('attn.c_proj.bias',768),('ln_2.weight',768),('ln_2.bias',768),
                       ('mlp.c_fc.bias',3072),('mlp.c_proj.bias',768)]:
        parameters.append(tensor(prefix+name,(size,)))
for name in ['ln_f.weight','ln_f.bias']:
    parameters.append(tensor(name,(768,)))
np.concatenate(parameters).astype('<f8').tofile(out/'params.bin')
for start, stop, shape_id in [(0,25129,4),(25129,50257,5)]:
    filename = f'matrix-{len(matrices):02}.bin'
    embedding[start:stop].T.copy().astype('<f4').tofile(out/filename)
    matrices.append({'file':filename,'shape':shape_id})

table_words, unicode_version = pack_tokenizer(source, out)
(out/'layout.json').write_text(json.dumps({'schemaVersion':2,'model':'GPT-2 124M','contextTokens':128,
    'shaderCompiler':'lean-body-wgsl','shaderEntryPoint':'lean_kernel',
    'shapes':[{'inner':k,'cols':n,'shader':f'kernel-{i}.wgsl'} for i,(k,n) in enumerate(shapes)],
    'matrices':matrices,'parameterOffsets':offsets,'unicodeVersion':unicode_version,
    'source':json.loads((source/'source.json').read_text()),
    'proofStatus':'Incomplete: demo model, tokenizer, transfer adapter, and complete schedule are not proved.'},indent=2)+'\n')
print(f'Packed 50 matrices, {table_words} tokenizer words, and pretrained parameters into {out}')
