#!/usr/bin/env python3
"""Offline checkpoint/table packing. No Python is used by inference."""
from pathlib import Path
import hashlib
import json
import sys
import unicodedata
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

# Reconstruct OpenAI's byte-to-Unicode alphabet and merge ranks.
alphabet = list(range(33,127))+list(range(161,173))+list(range(174,256))
for b in range(256):
    if b not in alphabet:
        alphabet.append(b)
n = 0
characters = []
for b in alphabet:
    if b in list(range(33,127))+list(range(161,173))+list(range(174,256)):
        characters.append(b)
    else:
        characters.append(256+n); n += 1
byte_encoder = dict(zip(alphabet,map(chr,characters)))
byte_decoder = {v:k for k,v in byte_encoder.items()}
vocab = json.loads((source/'vocab.json').read_text())
assert len(vocab) == 50257
merge_offset = 264
category_offset = merge_offset+2*131072
decode_offset = category_offset+0x110000
data_offset = decode_offset+50258
table = [0x47505432,131072,merge_offset,category_offset,decode_offset,data_offset,0,0]
table += [vocab[byte_encoder[b]] for b in range(256)]
table += [0]*(2*131072)
merges = [line.split() for line in (source/'merges.txt').read_text().splitlines()[1:] if line]
assert len(merges) == 50000
for rank, (a,b) in enumerate(merges):
    left,right,merged = vocab[a],vocab[b],vocab[a+b]
    assert merged == rank+256  # The Lean tokenizer compares these IDs as ranks.
    slot = (((left*65599)^right)*2654435761)&131071
    while table[merge_offset+2*slot]: slot = (slot+1)&131071
    table[merge_offset+2*slot:merge_offset+2*slot+2] = [left*65536+right+1,merged]
for cp in range(0x110000):
    char = chr(cp); category = unicodedata.category(char)[0]
    # Unicode White_Space, as used by the GPT-2 regex (excludes C0 separators).
    space = cp in range(9,14) or cp in [32,133,160,5760,8232,8233,8239,8287,12288] or 8192 <= cp <= 8202
    table.append(3 if space else 1 if category == 'L' else 2 if category == 'N' else 0)
decode_data, decode_starts = [], [0]
for token,_ in sorted(vocab.items(), key=lambda item:item[1]):
    decode_data.extend(byte_decoder[c] for c in token)
    decode_starts.append(len(decode_data))
table += decode_starts+decode_data
np.asarray(table,dtype='<u8').tofile(out/'tokenizer.bin')
(out/'layout.json').write_text(json.dumps({'schemaVersion':2,'model':'GPT-2 124M','contextTokens':128,
    'shaderCompiler':'lean-body-wgsl','shaderEntryPoint':'lean_kernel',
    'shapes':[{'inner':k,'cols':n,'shader':f'kernel-{i}.wgsl'} for i,(k,n) in enumerate(shapes)],
    'matrices':matrices,'parameterOffsets':offsets,'unicodeVersion':unicodedata.unidata_version,
    'source':json.loads((source/'source.json').read_text()),
    'proofStatus':'Incomplete: demo model, tokenizer, transfer adapter, and complete schedule are not proved.'},indent=2)+'\n')
print(f'Packed 50 matrices, {len(table)} tokenizer words, and pretrained parameters into {out}')
