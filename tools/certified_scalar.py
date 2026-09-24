#!/usr/bin/env python3
"""Fail-closed scalar64 packages. Generation is untrusted; verification invokes
Lean on canonical, data-derived propositions and never invokes the encoder."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
PROOF = ROOT / 'proofs/talos/lean'
PREFIX = 'Project.Correct.Scalar64.'
PILOTS = {
    'affine': ('Arithmetic', 'affine', 2, 'Pilots'),
    'choose': ('Arithmetic', 'choose', 2, 'Pilots'),
    'mix': ('Prng', 'mix', 1, 'Pilots'),
    'helper': ('ScalarHelper', 'caller', 2, 'Pilots'),
    'gcd': ('TalosGcd', 'gcd', 2, 'Gcd'),
}
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
BIN = {'add', 'sub', 'mul', 'divU', 'remU', 'bitAnd', 'bitOr', 'bitXor', 'shiftLeft', 'shiftRight'}
COREBIN = (BIN - {'divU', 'remU'}) | {'div', 'mod', 'min', 'max'}
IDENT = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
THEOREMS = ['ScalarPackageCheck.correctness', 'ScalarPackageCheck.closed', 'ScalarPackageCheck.coreMatches', 'ScalarPackageCheck.irMatches']
FILES = {'program.wasm', 'translation.json', 'decoded.json', 'source.lean', 'Check.lean'}

class Rejected(Exception):
    pass

def require(ok, why):
    if not ok:
        raise Rejected(why)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def canonical(data):
    return (json.dumps(data, sort_keys=True, indent=2, ensure_ascii=True) + '\n').encode()

def read_json(path):
    def obj(pairs):
        d = {}
        for k, v in pairs:
            require(k not in d, 'duplicate JSON key')
            d[k] = v
        return d
    require(path.stat().st_size < 2_000_000, 'package JSON too large')
    return json.loads(path.read_text(), object_pairs_hook=obj)

def keys(d, expected):
    require(type(d) is dict and set(d) == set(expected.split()), 'unexpected data fields')

def nat(n, limit=2**32):
    require(type(n) is int and 0 <= n < limit, 'invalid natural number')
    return str(n)

def ident(s):
    require(type(s) is str and IDENT.fullmatch(s) and '_' not in s.split('.'), 'invalid Lean identifier')
    return s

def string(s):
    require(type(s) is str and s.isascii() and all(32 <= ord(c) < 127 for c in s), 'non-ASCII/control string')
    return json.dumps(s)

def boolean(b):
    require(type(b) is bool, 'invalid Boolean')
    return str(b).lower()

def array(xs, render):
    require(type(xs) is list and len(xs) < 10000, 'invalid list')
    return '[' + ', '.join(render(x) for x in xs) + ']'

def ast(x, kind='expr', depth=0):
    require(depth < 128 and type(x) is list and x and type(x[0]) is str, 'invalid scalar syntax')
    tag, *a = x
    def child(v, k=kind):
        return ast(v, k, depth+1)
    if kind == 'expr':
        arities = {'get':1, 'const':1, 'bconst':1, 'bin':3, 'eq':2, 'ne':2, 'ltU':2, 'leU':2, 'not':1, 'and':2, 'or':2, 'ite':3}
        require(tag in arities and len(a) == arities[tag], 'unsupported scalar expression')
        if tag in {'get','const'}: vals = [nat(a[0], 2**64 if tag == 'const' else 2**32)]
        elif tag == 'bconst': vals = [boolean(a[0])]
        elif tag == 'bin':
            require(a[0] in BIN, 'unsupported scalar operation')
            vals = ['.'+a[0], child(a[1]), child(a[2])]
        else: vals = list(map(child,a))
    elif kind == 'command':
        arities = {'skip':0,'assign':2,'seq':2,'branch':3,'loop':2,'call':3}
        require(tag in arities and len(a) == arities[tag], 'unsupported command')
        if tag == 'skip': vals=[]
        elif tag == 'assign': vals=[nat(a[0]),child(a[1],'expr')]
        elif tag == 'seq': vals=list(map(child,a))
        elif tag in {'branch','loop'}: vals=[child(a[0],'expr')] + list(map(child,a[1:]))
        else: vals=[nat(a[0]),nat(a[1]),array(a[2],lambda v:child(v,'expr'))]
    else:
        arities={'var':1,'word':1,'bool':1,'letE':2,'ifE':3,'wordBin':3,'wordCmp':3,'call':2}
        require(tag in arities and len(a)==arities[tag], 'unsupported source core form')
        if tag=='var': vals=[nat(a[0])]
        elif tag=='word': vals=['.w64',nat(a[0],2**64)]
        elif tag=='bool': vals=[boolean(a[0])]
        elif tag in {'wordBin','wordCmp'}:
            require(a[0] in (COREBIN if tag=='wordBin' else {'eq','lt','le'}), 'unsupported core operation')
            vals=['.w64','.'+a[0],child(a[1]),child(a[2])]
        elif tag=='call': vals=[nat(a[0]),array(a[1],child)]
        else: vals=list(map(child,a))
    return '(.'+tag+(' '+ ' '.join(vals) if vals else '')+')'

def function(f):
    keys(f,'arity locals scratch body result')
    return '{ arity := '+nat(f['arity'])+', localCount := '+nat(f['locals'])+', scratch := '+nat(f['scratch'])+', body := '+ast(f['body'],'command')+', result := '+ast(f['result'])+' }'

# An untrusted binary reader is used only at compilation to produce a witness.
# Verification checks that witness against the independent, proved Lean decoder.
OPCODES={0x45:'i32Eqz',0x51:'i64Eq',0x52:'i64Ne',0x54:'i64LtU',0x58:'i64LeU',0x7c:'i64Add',0x7d:'i64Sub',0x7e:'i64Mul',0x80:'i64DivU',0x82:'i64RemU',0x83:'i64And',0x84:'i64Or',0x85:'i64Xor',0x86:'i64Shl',0x88:'i64ShrU'}
INDICES={0x0c:'br',0x0d:'brIf',0x10:'call',0x20:'localGet',0x21:'localSet'}
class Reader:
    def __init__(self,data): self.data,self.i=data,0
    def byte(self):
        require(self.i<len(self.data),'truncated WASM')
        b=self.data[self.i]; self.i+=1; return b
    def take(self,n):
        require(0<=n<=len(self.data)-self.i,'truncated WASM')
        b=self.data[self.i:self.i+n]; self.i+=n; return b
    def leb(self,signed=False):
        n=shift=0
        for _ in range(10):
            b=self.byte(); n|=(b&127)<<shift; shift+=7
            if b<128: return n-(1<<shift) if signed and b&64 else n
        raise Rejected('oversized LEB')
    def vector(self,read): return [read() for _ in range(self.leb())]
    def end(self): require(self.i==len(self.data),'unconsumed WASM data')
    def instrs(self):
        result=[]
        while True:
            op=self.byte()
            if op in {0x0b,0x05}: return result,op
            if op in OPCODES: result.append([OPCODES[op]])
            elif op in INDICES: result.append([INDICES[op],self.leb()])
            elif op in {0x41,0x42}: result.append(['i32Const' if op==0x41 else 'i64Const',self.leb(True)])
            elif op in {2,3,4}:
                bt=self.byte(); require(bt in {0x40,0x7e,0x7f},'unsupported control type')
                body,end=self.instrs(); t={0x40:'empty',0x7e:'i64',0x7f:'i32'}[bt]
                if op==4:
                    other=None
                    if end==5: other,end=self.instrs()
                    result.append(['iff',t,body,other])
                else: result.append(['block' if op==2 else 'loop',t,body])
                require(end==11,'invalid structured control')
            else: raise Rejected('opcode outside scalar64')

def decode_witness(data):
    r=Reader(data); require(r.take(8)==b'\x00asm\x01\x00\x00\x00','bad WASM header')
    sections=[]
    for sid in [1,3,7,10]:
        require(r.byte()==sid,'unexpected scalar section')
        s=Reader(r.take(r.leb())); sections.append(s)
    r.end(); t,f,e,c=sections
    def typ():
        require(t.byte()==0x60,'bad function type')
        params=t.vector(t.byte); results=t.vector(t.byte)
        require(all(x==0x7e for x in params) and results==[0x7e],'non-scalar signature')
        return len(params)
    types=t.vector(typ); fns=f.vector(f.leb)
    def export():
        name=list(e.take(e.leb())); require(e.byte()==0,'non-function export')
        return {'name':bytes(name).decode('ascii'),'index':e.leb()}
    exports=e.vector(export)
    def code():
        b=Reader(c.take(c.leb()))
        def local():
            count=b.leb(); require(b.byte()==0x7e,'non-scalar local'); return count
        locals_=b.vector(local); body,end=b.instrs(); require(end==11,'bad code end'); b.end()
        return {'locals':locals_,'body':body}
    codes=c.vector(code)
    for s in sections:s.end()
    return {'types':types,'functions':fns,'exports':exports,'codes':codes}

def instruction(x,depth=0):
    require(depth<128 and type(x) is list and x,'invalid decoded instruction')
    tag,*a=x
    def body(xs):return array(xs,lambda v:instruction(v,depth+1))
    if tag in OPCODES.values(): require(not a,'unexpected instruction argument'); vals=[]
    elif tag in INDICES.values(): require(len(a)==1,'bad index'); vals=[nat(a[0])]
    elif tag in {'i32Const','i64Const'}:
        require(len(a)==1 and type(a[0]) is int and -(2**63)<=a[0]<2**63,'bad constant')
        vals=['('+str(a[0])+')']
    elif tag in {'block','loop','iff'}:
        require(len(a)==(3 if tag=='iff' else 2) and a[0] in {'empty','i64','i32'},'bad control')
        vals=['.empty' if a[0]=='empty' else '(.value .'+a[0]+')',body(a[1])]
        if tag=='iff':vals+=['none' if a[2] is None else '(some '+body(a[2])+')']
    else:raise Rejected('unsupported decoded instruction')
    return '(.'+tag+(' '+' '.join(vals) if vals else '')+')'

def raw_module(d):
    keys(d,'types functions exports codes')
    def typ(n):return '{ params := List.replicate '+nat(n)+' .i64, results := [.i64] }'
    def exp(e):
        keys(e,'name index'); name=string(e['name'])
        return '{ name := { bytes := '+array(list(e['name'].encode()),nat)+', text := '+name+' }, desc := .func '+nat(e['index'])+' }'
    def code(c):
        keys(c,'locals body')
        return '{ locals := '+array(c['locals'],lambda n:'{ count := '+nat(n)+', type := .i64 }')+', body := '+array(c['body'],instruction)+' }'
    return '{ sections := [.type, .function, .export, .code], types := '+array(d['types'],typ)+', functionTypeIndices := '+array(d['functions'],nat)+', memories := [], globals := [], exports := '+array(d['exports'],exp)+', codes := '+array(d['codes'],code)+' }'

def input_abi(arity,source):
    nat(arity,33)
    if arity==0:return 'Unit','fun _ => []','fun _ => '+source
    if arity==1:return 'UInt64','fun input => [input]',source
    projections=['input'+'.2'*i+('.1' if i<arity-1 else '') for i in range(arity)]
    return ' × '.join(['UInt64']*arity),'fun input => ['+', '.join(projections)+']','fun input => '+source+' '+' '.join(projections)

def checking_text(m,t,raw,data):
    keys(t,'functions core signatures core_entry entry export arity')
    require(t['arity']==m['arity'],'ABI arity mismatch')
    inp,args,source=input_abi(m['arity'],ident(m['source']))
    return f'''import {ident(m['source_module'])}
import {ident(m['certificate_module'])}
import Project.Correct.Scalar64.Certificate

namespace ScalarPackageCheck
open Project.Correct.Scalar64
open Wasm.Binary
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

def claim : Certificate ({inp}) ({args}) ({source}) := {ident(m['certificate'])}
def bytes : ByteArray := ByteArray.mk #{array(list(data),nat)}
def raw : RawModule := {raw_module(raw)}
theorem coreMatches : claim.core = {array(t['core'],lambda x:ast(x,'core'))} := by rfl
theorem signaturesMatch : claim.signatures = {array(t['signatures'],lambda n:'{ params := List.replicate '+nat(n)+' (.word .w64), result := .word .w64 }')} := by rfl
theorem coreEntryMatches : claim.coreEntry = {nat(t['core_entry'])} := by rfl
theorem irMatches : claim.functions = {array(t['functions'],function)} := by rfl
theorem entryMatches : claim.entry = {nat(t['entry'])} := by rfl
theorem exportMatches : claim.exportName = {string(t['export'])} := by rfl
theorem arityMatches : claim.function.arity = {nat(t['arity'])} := by rfl
theorem decoded : decode bytes = .ok raw := by cbv
theorem validated : Validator.validateRaw raw = .ok () := by rfl
theorem translated : Translation.module raw = claim.module := by rfl
theorem closed : Artifact claim bytes := Artifact.of_parts claim decoded validated translated

def correctness (α : Type) := Artifact.valid_and_correct (α := α) claim closed
#print axioms correctness
#print axioms coreMatches
#print axioms signaturesMatch
#print axioms irMatches
#print axioms closed
end ScalarPackageCheck
'''


def git(*args, cwd=ROOT):
    p=subprocess.run(['git',*args],cwd=cwd,capture_output=True)
    require(p.returncode==0,'git '+args[0]+' failed: '+p.stderr.decode())
    return p.stdout.decode().strip()

def lean(args, timeout=180):
    cmd=[str(ROOT/'tools/leanrun'),'--timeout',str(timeout),'lake',*args]
    p=subprocess.run(cmd,cwd=PROOF,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
    require(p.returncode==0,'Lean check failed:\n'+p.stdout[-14000:])
    require('declaration uses \'sorry\'' not in p.stdout,'Lean reported sorry')
    return p.stdout

def pins():
    return {p:sha((ROOT/p).read_bytes()) for p in ['lean-toolchain','lakefile.lean','lake-manifest.json','proofs/talos/lean/lakefile.toml','proofs/talos/lean/lake-manifest.json']}

def check_checkout(revision,expected_pins):
    require(re.fullmatch('[0-9a-f]{40}',revision) is not None,'invalid revision')
    require(expected_pins==pins(),'toolchain/dependency pin mismatch')
    # Documentation commits may follow the package revision; proof/config/code may not differ.
    paths=['LeanExe.lean','Main.lean','LeanExe','proofs/talos/lean/Project',
           'lean-toolchain','lakefile.lean','lake-manifest.json',
           'proofs/talos/lean/lean-toolchain','proofs/talos/lean/lakefile.toml',
           'proofs/talos/lean/lake-manifest.json',
           'tools/certified_scalar.py','tools/compile-certified','tools/verify-certified']
    require(not git('diff','--name-only',revision,'--',*paths),'checkout differs from certified source revision')
    deps=json.loads((PROOF/'lake-manifest.json').read_text())['packages']
    for dep in deps:
        if dep['type']=='git':
            p=PROOF/'.lake/packages'/dep['name']
            require(git('rev-parse','HEAD',cwd=p)==dep['rev'],'dependency revision mismatch: '+dep['name'])
            require(not git('diff','--name-only','HEAD','--','*.lean','**/*.lean','*lakefile*','**/*lakefile*',cwd=p),'modified dependency: '+dep['name'])
    version=lean(['env','lean','--version'],30)
    require('4.34.0-rc2' in version and '6a10ac8' in version,'wrong Lean executable')

def audit(output):
    matches=re.findall(r"'ScalarPackageCheck\.[^']+' depends on axioms: \[([^]]*)\]",output)
    require(len(matches)==5,'missing axiom audits')
    for line in matches:
        axioms={s.strip() for s in line.split(',') if s.strip()}
        require(axioms<=ALLOWED_AXIOMS,'unapproved axiom: '+str(axioms-ALLOWED_AXIOMS))

def verify(directory):
    directory=Path(directory).resolve(); m=read_json(directory/'manifest.json')
    keys(m,'schema profile repository revision pins source_module source certificate_module certificate arity abi theorems files')
    require(type(m['schema']) is int and m['schema']==1 and m['profile']=='scalar64' and m['repository']=='jsmorph/leanexe','unsupported manifest')
    for name in ['source_module','source','certificate_module','certificate']:ident(m[name])
    require(m['source'].startswith(m['source_module']+'.'), 'source declaration is outside its named module namespace')
    nat(m['arity'],33)
    require(m['theorems']==THEOREMS,'unexpected theorem declarations')
    require(m['abi']=={'params':['i64']*m['arity'],'result':'i64','argument_order':list(range(m['arity']))},'unsupported ABI')
    require(type(m['files']) is dict and set(m['files'])==FILES,'unexpected package file set')
    require({p.name for p in directory.iterdir()}==FILES|{'manifest.json'},'extra/missing package files')
    for name,digest in m['files'].items():
        p=directory/name
        require(p.is_file() and not p.is_symlink() and p.stat().st_size<2_000_000,'invalid package file')
        require(sha(p.read_bytes())==digest,'hash mismatch: '+name)
    check_checkout(m['revision'],m['pins'])
    src=m['source_module'].replace('.','/')+'.lean'
    require(src.startswith('LeanExe/') and m['certificate_module'].startswith('Project.'),'unsupported source/module namespace')
    require(git('ls-files','--error-unmatch',src)==src,'source is not tracked')
    require((directory/'source.lean').read_bytes()==(ROOT/src).read_bytes(),'source snapshot mismatch')
    cert='proofs/talos/lean/'+m['certificate_module'].replace('.','/')+'.lean'
    require(git('ls-files','--error-unmatch',cert)==cert,'certificate module is not tracked')
    data=(directory/'program.wasm').read_bytes()
    text=checking_text(m,read_json(directory/'translation.json'),read_json(directory/'decoded.json'),data)
    require((directory/'Check.lean').read_text()==text,'noncanonical checker text')
    # Only checked data is elaborated. Package-supplied tactics or arbitrary Lean are never executed.
    lean(['build',m['certificate_module']])
    with tempfile.TemporaryDirectory(prefix='scalar-check-',dir=PROOF/'.lake') as tmp:
        p=Path(tmp)/'Check.lean';p.write_text(text)
        output=lean(['env','lean',str(p)])
        audit(output)
    print('verified scalar64:',m['source'],'→',sha(data),flush=True)
    return m

def compile_package(options):
    require(options.profile=='scalar64','unsupported profile')
    if options.pilot:
        require(options.pilot in PILOTS,'source has no scalar64 certificate')
        mod,name,arity,cm=PILOTS[options.pilot]
        sm='LeanExe.Examples.'+mod; src=sm+'.'+name
        certmod=PREFIX+cm; cert=PREFIX+'Pilots.'+options.pilot+'Certificate'
    else:
        require(all([options.source_module,options.source,options.certificate_module,options.certificate]) and options.arity is not None,'provide a pilot or a complete source/certificate binding')
        sm,src,arity,certmod,cert=options.source_module,options.source,options.arity,options.certificate_module,options.certificate
    for s in [sm,src,certmod,cert]:ident(s)
    nat(arity,33)
    directory=Path(options.output).resolve()
    require(not directory.exists(),'output already exists')
    m={'schema':1,'profile':'scalar64','repository':'jsmorph/leanexe','revision':git('rev-parse','HEAD'),'pins':pins(),
       'source_module':sm,'source':src,'certificate_module':certmod,'certificate':cert,'arity':arity,
       'theorems':THEOREMS,'abi':{'params':['i64']*arity,'result':'i64','argument_order':list(range(arity))}}
    check_checkout(m['revision'],m['pins'])
    lean(['build',certmod]);lean(['build',PREFIX+'Package'])
    inp,args,source=input_abi(arity,src)
    with tempfile.TemporaryDirectory(prefix='scalar-emit-',dir=PROOF/'.lake') as tmp:
        staging=Path(tmp)/'package'
        code=f'import {certmod}\nimport {sm}\nimport {PREFIX}Package\nopen Project.Correct.Scalar64\ndef claim : Certificate ({inp}) ({args}) ({source}) := {cert}\ndef main : IO Unit := Package.emit claim {string(str(staging))}\n'
        p=Path(tmp)/'Emit.lean';p.write_text(code)
        lean(['env','lean','--run',str(p)])
        data=(staging/'program.wasm').read_bytes()
        raw=decode_witness(data);(staging/'decoded.json').write_bytes(canonical(raw))
        srcpath=ROOT/(sm.replace('.','/')+'.lean')
        require(srcpath.is_relative_to(ROOT/'LeanExe'),'unsupported source module')
        (staging/'source.lean').write_bytes(srcpath.read_bytes())
        text=checking_text(m,read_json(staging/'translation.json'),raw,data)
        (staging/'Check.lean').write_text(text)
        m['files']={f:sha((staging/f).read_bytes()) for f in sorted(FILES)}
        (staging/'manifest.json').write_bytes(canonical(m))
        verify(staging)
        # Publish only after the independent verifier has accepted every obligation.
        directory.parent.mkdir(parents=True,exist_ok=True)
        import shutil
        shutil.copytree(staging,directory)
    print('certified package:',directory,flush=True)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    commands=p.add_subparsers(dest='command',required=True)
    c=commands.add_parser('compile');c.add_argument('pilot',nargs='?')
    c.add_argument('--profile',required=True);c.add_argument('--output',required=True)
    for name in ['source-module','source','certificate-module','certificate']:c.add_argument('--'+name)
    c.add_argument('--arity',type=int)
    v=commands.add_parser('verify');v.add_argument('package')
    o=p.parse_args()
    try:
        if o.command=='compile':compile_package(o)
        else:verify(o.package)
    except (Rejected,OSError,ValueError,RecursionError,TypeError,KeyError,IndexError) as e:
        print('rejected:',e,file=sys.stderr);return 1
    return 0

if __name__=='__main__':sys.exit(main())
