#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),assert=require('node:assert/strict'),path=require('node:path');
const {runChecked}=require('../tools/run-process');
const {callI64Slots}=require('../tools/wasmtime-host');
const b=Buffer.alloc(8),bits=x=>{b.writeDoubleLE(x);return b.readBigUInt64LE();},value=x=>{b.writeBigUInt64LE(x);return b.readDoubleLE();};
function reference(words,side,NumericalRejection){
 try {
  const q=words.map(value),out=side(q);
  return [0n,...[out.u,out.p,out.speed,...out.flux].map(bits)];
 }catch(error){
  if(!(error instanceof NumericalRejection))throw error;
  return[1n,0n,0n,0n,0n,0n,0n,0n];
 }
}
async function main(){
 const {side,NumericalRejection,riemannPrimitives,conservative}=await import('../tools/euler-2d-oracle.mjs');
 const directory=fs.mkdtempSync(path.join('tmp','euler-2d-conservative-'));
 const moduleName='LeanExe.Examples.Euler2DConservative',entry=moduleName+'.sideCheckedBits';
 const compiler=process.env.LEAN_WASM_EXE||path.join('.lake','build','bin','lean-wasm');
 for(const [command,file]of [['compile','program.wasm'],['compile-wat','program.wat']])runChecked([compiler,command,'--module',moduleName,'--entry',entry,'--out',path.join(directory,file)],{encoding:'utf8',timeout:120000});
 const wat=fs.readFileSync(path.join(directory,'program.wat'),'utf8');
 for(const [op,count]of [['sub',2],['div',3],['mul',11],['add',5],['sqrt',1]])assert.equal((wat.match(new RegExp('f64\\.'+op+'\\b','g'))||[]).length,count,'WAT '+op);
 const one=bits(1),E=bits(2.5),sign=1n<<63n,max=0x7fefffffffffffffn;
 const cases=[
  ['stationary left',[one,0n,0n,E],0],['stationary right',[bits(.125),0n,0n,bits(.25)],0],
  ['moving both components',[one,bits(.5),bits(-.75),E],0],['transverse-only energy',[one,0n,one,E],0],
  ['both magnitude boundaries',[one,one,one|sign,one+1n],0],['both signed zero',[one,sign,sign,E],0],
  ['least subnormal density',[1n,0n,0n,2n],0],
  ['zero density',[0n,0n,0n,E],1],['negative zero density',[sign,0n,0n,E],1],
  ['negative density',[one|sign,0n,0n,E],1],['energy equals density',[one,0n,0n,one],0],
  ['energy adjacent below density',[one,0n,0n,one-1n],0],['normal adjacent above unit speed',[one,one+1n,0n,E],0],
  ['transverse adjacent above unit speed',[one,0n,one+1n,E],0],['negative transverse above unit speed',[one,0n,(one+1n)|sign,E],0],
  ['zero internal energy',[one,bits(2),0n,bits(2)],1],
  ['negative internal energy',[one,bits(2),bits(1),bits(2)],1],
  ['below certified residual margin',[one,bits(2),0n,bits(2+2**-49)],1],
  ['above certified residual margin',[one,bits(2),0n,bits(2+2**-42)],0],
  ['large common scale',[bits(1e300),bits(1.206e300),0n,bits(2e300)],0],
  ['small common scale',[bits(1e-300),bits(1.206e-300),0n,bits(2e-300)],0],
  ['rounded pressure underflow',[1n,1n,1n,2n],1],['pressure ratio overflow',[1n,0n,0n,one],1],
  ['enthalpy overflow',[one,0n,0n,max],1],['zero energy',[one,0n,0n,0n],1],['negative zero energy',[one,0n,0n,sign],1],
 ];
 for(const [index,q]of riemannPrimitives.entries())cases.push(['Riemann quadrant '+index,conservative(q).map(bits),0]);
 for(const special of [0x7ff0000000000000n,0xfff0000000000000n,0x7ff0000000000001n,0xfff0000000000001n,0x7ff8000000000000n,0xfff8000000000000n])for(let slot=0;slot<4;slot++){const q=[one,0n,0n,E];q[slot]=special;cases.push(['nonfinite slot'+slot,q,1]);}
 for(const [name,q,status]of cases){const expected=reference(q,side,NumericalRejection);assert.equal(expected[0],BigInt(status),'reference classification '+name);const actual=callI64Slots(path.join(directory,'program.wasm'),'sideCheckedBits',8,q);assert.deepEqual(actual,expected,name);}
 console.log('Checked '+cases.length+' two-dimensional sides through Wasmtime, all raw output words and opcode counts; retained '+directory);
}
main().catch(error=>{console.error(error.stack);process.exitCode=1;});
