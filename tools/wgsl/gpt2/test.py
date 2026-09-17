#!/usr/bin/env python3
"""Focused boundary/integrity checks. No inference implementation in this test."""
from pathlib import Path
import json
import os
import struct
import subprocess
import tempfile

root = Path(__file__).resolve().parents[3]
bundle = root/'build/gpt2/bundle'
work = Path(tempfile.mkdtemp(prefix='checks-',dir=root/'build/gpt2'))
def bits(x): return str(struct.unpack('<Q',struct.pack('<d',x))[0])
def call(op,x,aux,params,position):
    source,target = work/'input.json',work/'output.json'
    source.write_text(json.dumps(dict(op=op,x=x,aux=aux,params=params,position=position)))
    subprocess.run(['node',str(root/'tools/wgsl/gpt2/wasm-call.mjs'),str(bundle/'model.wasm'),str(source),str(target)],check=True)
    return json.loads(target.read_text())

# At position 127, all equal attention scores yield exactly 1/128. Cached
# values 0..126 and current value 127 therefore average to exactly 63.5.
cache = ['0']*(128*768)
for t in range(128): cache += [bits(t)]*768
bias = ['0']*1536+[bits(127)]*768
actual = call(2,['0']*2304,cache,bias,127)
assert actual == ['0']*768+[bits(127)]*768+[bits(63.5)]*768
assert call(2,['0']*2304,cache,bias,128) == []

invalid = [(['--prompt',''],'prompt'),(['--prompt',' a'*127,'--generate','2'],'128-token'),
    (['--prompt','hello','--seed','0'],'seed'),(['--prompt','hello','--temperature','-1'],'temperature')]
for args,message in invalid:
    p = subprocess.run([str(root/'tools/gpt2'),'run',*args],capture_output=True,text=True)
    assert p.returncode != 0 and message in p.stderr,(args,p.stderr)

changed = work/'changed'; changed.mkdir()
for file in bundle.iterdir():
    if file.is_file() and file.name != 'kernel-0.wgsl': (changed/file.name).symlink_to(file)
shader = bytearray((bundle/'kernel-0.wgsl').read_bytes()); shader[0] ^= 1
(changed/'kernel-0.wgsl').write_bytes(shader)
env = dict(os.environ,LEANEXE_GPT2_BUNDLE=str(changed))
p = subprocess.run([str(root/'tools/gpt2'),'run','--prompt','hello','--generate','1'],env=env,capture_output=True,text=True)
assert p.returncode != 0 and 'SHA-256 differs' in p.stderr,p.stderr
report = dict(attentionPosition127='exact',attentionPosition128='rejected',invalidRequests=len(invalid),changedShader='rejected')
(work/'result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report)); print(work)
