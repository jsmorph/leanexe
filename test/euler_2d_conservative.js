#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),assert=require('node:assert/strict'),path=require('node:path');
const {runChecked}=require('../tools/run-process');
const {callI64Slots}=require('../tools/wasmtime-host');
const b=Buffer.alloc(8),bits=x=>{b.writeDoubleLE(x);return b.readBigUInt64LE();},value=x=>{b.writeBigUInt64LE(x);return b.readDoubleLE();};
const finite=x=>{assert.ok(Number.isFinite(x));return x;},positive=x=>{finite(x);assert.ok(x>0);return x;};
function reference(words){
 try {
  const [r,m,t,E]=words.map(value);positive(r);finite(m);finite(t);positive(E);
  assert.ok(Math.abs(m)<=r&&Math.abs(t)<=r&&r<E);
  const u=finite(m/r),mu=finite(m*u),v=finite(t/r),tv=finite(t*v);
  const ks=finite(mu+tv),half=finite(.5*ks),internal=positive(E-half);
  const p=positive(.4*internal),pr=positive(p/r),rad=positive(1.4*pr),c=positive(Math.sqrt(rad));
  const speed=positive(Math.abs(u)+c),fm=finite(mu+p),ft=finite(t*u),ep=finite(E+p),fe=finite(u*ep);
  return[0n,...[u,p,speed,m,fm,ft,fe].map(bits)];
 }catch{return[1n,0n,0n,0n,0n,0n,0n,0n];}
}
async function main(){
 const directory=fs.mkdtempSync(path.join('tmp','euler-2d-conservative-'));
 const moduleName='LeanExe.Examples.Euler2DConservative',entry=moduleName+'.sideCheckedBits';
 const compiler=process.env.LEAN_WASM_EXE||path.join('.lake','build','bin','lean-wasm');
 for(const [command,file]of [['compile','program.wasm'],['compile-wat','program.wat']])runChecked([compiler,command,'--module',moduleName,'--entry',entry,'--out',path.join(directory,file)],{encoding:'utf8',timeout:120000});
 const wat=fs.readFileSync(path.join(directory,'program.wat'),'utf8');
 for(const [op,count]of [['sub',1],['div',3],['mul',7],['add',4],['sqrt',1]])assert.equal((wat.match(new RegExp('f64\\.'+op+'\\b','g'))||[]).length,count,'WAT '+op);
 const one=bits(1),E=bits(2.5),sign=1n<<63n,max=0x7fefffffffffffffn;
 const cases=[
  ['stationary left',[one,0n,0n,E],0],['stationary right',[bits(.125),0n,0n,bits(.25)],0],
  ['moving both components',[one,bits(.5),bits(-.75),E],0],['transverse-only energy',[one,0n,one,E],0],
  ['both magnitude boundaries',[one,one,one|sign,one+1n],0],['both signed zero',[one,sign,sign,E],0],
  ['least subnormal density',[1n,0n,0n,2n],0],
  ['zero density',[0n,0n,0n,E],1],['negative zero density',[sign,0n,0n,E],1],
  ['negative density',[one|sign,0n,0n,E],1],['strict energy boundary',[one,0n,0n,one],1],
  ['energy adjacent below',[one,0n,0n,one-1n],1],['normal adjacent outside',[one,one+1n,0n,E],1],
  ['transverse adjacent outside',[one,0n,one+1n,E],1],['negative transverse adjacent outside',[one,0n,(one+1n)|sign,E],1],
  ['rounded pressure underflow',[1n,1n,1n,2n],1],['pressure ratio overflow',[1n,0n,0n,one],1],
  ['enthalpy overflow',[one,0n,0n,max],1],['zero energy',[one,0n,0n,0n],1],['negative zero energy',[one,0n,0n,sign],1],
 ];
 for(const special of [0x7ff0000000000000n,0xfff0000000000000n,0x7ff0000000000001n,0xfff0000000000001n,0x7ff8000000000000n,0xfff8000000000000n])for(let slot=0;slot<4;slot++){const q=[one,0n,0n,E];q[slot]=special;cases.push(['nonfinite slot'+slot,q,1]);}
 for(const [name,q,status]of cases){const expected=reference(q);assert.equal(expected[0],BigInt(status),'reference classification '+name);const actual=callI64Slots(path.join(directory,'program.wasm'),'sideCheckedBits',8,q);assert.deepEqual(actual,expected,name);}
 console.log('Checked '+cases.length+' two-dimensional sides through Wasmtime, all raw output words and opcode counts; retained '+directory);
}
main().catch(error=>{console.error(error.stack);process.exitCode=1;});
