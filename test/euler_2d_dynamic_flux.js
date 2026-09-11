#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),assert=require('node:assert/strict'),path=require('node:path');
const {runChecked}=require('../tools/run-process');
const {callI64Slots}=require('../tools/wasmtime-host');
const b=Buffer.alloc(8),bits=x=>{b.writeDoubleLE(x);return b.readBigUInt64LE();},value=x=>{b.writeBigUInt64LE(x);return b.readDoubleLE();};
async function main(){
 const {flux,NumericalRejection,riemannPrimitives,conservative}=await import('../tools/euler-2d-oracle.mjs');
 const reference=words=>{
  try{const q=words.map(value),out=flux(q.slice(0,4),q.slice(4));return[0n,...out.value.map(bits),bits(out.alpha)];}
  catch(error){if(!(error instanceof NumericalRejection))throw error;return[1n,0n,0n,0n,0n,0n];}
 };
 const directory=fs.mkdtempSync(path.join('tmp','euler-2d-dynamic-flux-'));
 const moduleName='LeanExe.Examples.Euler2DDynamicFlux',entry=moduleName+'.fluxCheckedBits';
 const compiler=process.env.LEAN_WASM_EXE||path.join('.lake','build','bin','lean-wasm');
 for(const [command,file]of [['compile','program.wasm'],['compile-wat','program.wat']])runChecked([compiler,command,'--module',moduleName,'--entry',entry,'--out',path.join(directory,file)],{encoding:'utf8',timeout:120000});
 const wat=fs.readFileSync(path.join(directory,'program.wat'),'utf8');
 for(const [op,count]of [['sub',4],['div',3],['mul',14],['add',6],['sqrt',1]])assert.equal((wat.match(new RegExp('f64\\.'+op+'\\b','g'))||[]).length,count,'WAT '+op);
 const a=[1,0,0,2.5].map(bits),b=[.25,0,0,.625].map(bits),moving=[1,.5,-.75,2.5].map(bits);
 const one=bits(1),sign=1n<<63n;
 const cases=[['quadrant discontinuity',[...a,...b],0],['reversed discontinuity',[...b,...a],0],['equal moving state',[...moving,...moving],0],['transverse transport',[...moving,...a],0],['reversed transverse transport',[...a,...moving],0],['signed zero',[one,sign,sign,bits(2.5),...a],0],['adjacent energy',[one,0n,0n,one+1n,...a],0]];
 for(const [state,status] of [[[0n,0n,0n,bits(2.5)],1],[[sign,0n,0n,bits(2.5)],1],[[one,0n,0n,one],0],[[one,one+1n,0n,bits(2.5)],0],[[one,0n,(one+1n)|sign,bits(2.5)],0],[[1n,1n,1n,2n],1],[[1n,0n,0n,one],1],[[one,0n,0n,0x7fefffffffffffffn],1]]){
  cases.push(['left guard boundary',[...state,...a],status],['right guard boundary',[...a,...state],status]);
 }
 for(const [index,q]of riemannPrimitives.entries()){const state=conservative(q).map(bits);cases.push(['constant Riemann quadrant '+index,[...state,...state],0]);}
 for(const special of [0x7ff0000000000000n,0xfff0000000000000n,0x7ff0000000000001n,0xfff0000000000001n,0x7ff8000000000000n,0xfff8000000000000n])for(let slot=0;slot<8;slot++){const q=[...a,...b];q[slot]=special;cases.push(['nonfinite slot'+slot,q,1]);}
 for(const [name,q,status]of cases){const expected=reference(q);assert.equal(expected[0],BigInt(status),'reference '+name);assert.deepEqual(callI64Slots(path.join(directory,'program.wasm'),'fluxCheckedBits',6,q),expected,name);}
 console.log('Checked '+cases.length+' 2D directional fluxes through Wasmtime, all raw words and opcode counts; retained '+directory);
}
main().catch(error=>{console.error(error.stack);process.exitCode=1;});
