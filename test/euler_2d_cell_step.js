#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),assert=require('node:assert/strict'),path=require('node:path');
const {runChecked}=require('../tools/run-process');
const {callI64Slots}=require('../tools/wasmtime-host');
const buffer=Buffer.alloc(8),bits=x=>{buffer.writeDoubleLE(x);return buffer.readBigUInt64LE();},value=x=>{buffer.writeBigUInt64LE(x);return buffer.readDoubleLE();};
async function main(){
 const {cell,side,flux,NumericalRejection,riemannPrimitives,conservative}=await import('../tools/euler-2d-oracle.mjs');
 const reference=words=>{try{const q=words.map(value),out=cell(q[0],q.slice(1,5),q.slice(5,9),q.slice(9));return[0n,...[...out.state,out.p,out.alpha,out.courant].map(bits)];}catch(error){if(!(error instanceof NumericalRejection))throw error;return[1n,0n,0n,0n,0n,0n,0n,0n];}};
 const directory=fs.mkdtempSync(path.join('tmp','euler-2d-cell-step-'));
 const moduleName='LeanExe.Examples.Euler2DCellStep',entry=moduleName+'.cellCheckedBits';
 const compiler=process.env.LEAN_WASM_EXE||path.join('.lake','build','bin','lean-wasm');
 for(const [command,file]of [['compile','program.wasm'],['compile-wat','program.wat']])runChecked([compiler,command,'--module',moduleName,'--entry',entry,'--out',path.join(directory,file)],{encoding:'utf8',timeout:120000});
 const wat=fs.readFileSync(path.join(directory,'program.wat'),'utf8');
 for(const [op,count]of [['sub',6],['div',3],['mul',16],['add',6],['sqrt',1]])assert.equal((wat.match(new RegExp('f64\\.'+op+'\\b','g'))||[]).length,count,'WAT '+op);
 const a=[1,0,0,2.5].map(bits),b=[.25,0,0,.625].map(bits),moving=[1,.5,-.75,2.5].map(bits),ratio=bits(.2),one=bits(1),sign=1n<<63n;
 const cases=[['constant',[ratio,...a,...a,...a],0],['left discontinuity',[ratio,...a,...b,...b],0],['right discontinuity',[ratio,...a,...a,...b],0],['moving transverse',[ratio,...a,...moving,...a],0],['constant moving',[ratio,...moving,...moving,...moving],0],['signed zero',[ratio,...a,one,sign,sign,bits(2.5),...a],0],['subnormal ratio',[1n,...a,...a,...a],0]];
 const near=[one,0n,0n,one+1n],advecting=[one,one,0n,one+1n];
 side(near.map(value));side(advecting.map(value));
 assert.ok(.25*flux(near.map(value),advecting.map(value)).alpha<=.5);
 cases.push(['updated state accepted beyond old sufficient domain',[bits(.25),...near,...near,...advecting],0]);
 const ceiling=bits(.5/Math.sqrt(1.4));
 cases.push(['CFL ceiling',[ceiling,...a,...a,...a],0],['adjacent above CFL',[ceiling+2n,...a,...a,...a],1]);
 assert.equal(reference(cases.at(-2)[1])[7],bits(.5),'rounded exact ceiling');
 for(const badRatio of [0n,sign,one|sign,one,0x7ff0000000000000n,0xfff0000000000000n,0x7ff8000000000000n])cases.push(['invalid ratio',[badRatio,...a,...a,...a],1]);
 for(const [state,status] of [[[0n,0n,0n,bits(2.5)],1],[[one,0n,0n,one],0],[[one,one+1n,0n,bits(2.5)],0],[[one,0n,(one+1n)|sign,bits(2.5)],0],[[1n,1n,1n,2n],1]])for(let slot=0;slot<3;slot++){const q=[ratio,...a,...a,...a];q.splice(1+4*slot,4,...state);cases.push(['state guard boundary '+slot,q,status]);}
 for(const [index,q]of riemannPrimitives.entries()){const state=conservative(q).map(bits);cases.push(['constant Riemann quadrant '+index,[bits(.1),...state,...state,...state],0]);}
 for(const special of [0x7ff0000000000000n,0xfff0000000000000n,0x7ff0000000000001n,0xfff8000000000000n])for(let slot=1;slot<13;slot++){const q=[ratio,...a,...b,...b];q[slot]=special;cases.push(['nonfinite slot'+slot,q,1]);}
 for(const [name,q,status]of cases){const expected=reference(q);assert.equal(expected[0],BigInt(status),'reference '+name);assert.deepEqual(callI64Slots(path.join(directory,'program.wasm'),'cellCheckedBits',8,q),expected,name);}
 console.log('Checked '+cases.length+' 2D cells through Wasmtime, all raw words and opcode counts; retained '+directory);
}
main().catch(error=>{console.error(error.stack);process.exitCode=1;});
