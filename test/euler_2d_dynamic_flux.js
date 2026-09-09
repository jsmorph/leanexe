#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),assert=require('node:assert/strict'),path=require('node:path');
const {runChecked}=require('../tools/run-process');
const {callI64Slots}=require('../tools/wasmtime-host');
const b=Buffer.alloc(8),bits=x=>{b.writeDoubleLE(x);return b.readBigUInt64LE();},value=x=>{b.writeBigUInt64LE(x);return b.readDoubleLE();};
const finite=x=>{assert.ok(Number.isFinite(x));return x;},positive=x=>{finite(x);assert.ok(x>0);return x;};
function side(words){
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

function reference(words){
 try {
  const left=side(words.slice(0,4)),right=side(words.slice(4));
  assert.equal(left[0],0n);assert.equal(right[0],0n);
  const alpha=Math.max(value(left[3]),value(right[3]));
  const out=[];
  for(let j=0;j<4;j++){
   const sum=finite(value(left[4+j])+value(right[4+j])),mean=finite(.5*sum);
   const jump=finite(value(words[4+j])-value(words[j])),viscosity=finite(alpha*jump);
   const half=finite(.5*viscosity),result=finite(mean-half);out.push(bits(result));
  }
  return[0n,...out,bits(alpha)];
 }catch{return[1n,0n,0n,0n,0n,0n];}
}
function main(){
 const directory=fs.mkdtempSync(path.join('tmp','euler-2d-dynamic-flux-'));
 const moduleName='LeanExe.Examples.Euler2DDynamicFlux',entry=moduleName+'.fluxCheckedBits';
 const compiler=process.env.LEAN_WASM_EXE||path.join('.lake','build','bin','lean-wasm');
 for(const [command,file]of [['compile','program.wasm'],['compile-wat','program.wat']])runChecked([compiler,command,'--module',moduleName,'--entry',entry,'--out',path.join(directory,file)],{encoding:'utf8',timeout:120000});
 const wat=fs.readFileSync(path.join(directory,'program.wat'),'utf8');
 for(const [op,count]of [['sub',3],['div',3],['mul',10],['add',5],['sqrt',1]])assert.equal((wat.match(new RegExp('f64\\.'+op+'\\b','g'))||[]).length,count,'WAT '+op);
 const a=[1,0,0,2.5].map(bits),b=[.25,0,0,.625].map(bits),moving=[1,.5,-.75,2.5].map(bits);
 const one=bits(1),sign=1n<<63n;
 const cases=[['quadrant discontinuity',[...a,...b],0],['reversed discontinuity',[...b,...a],0],['equal moving state',[...moving,...moving],0],['transverse transport',[...moving,...a],0],['reversed transverse transport',[...a,...moving],0],['signed zero',[one,sign,sign,bits(2.5),...a],0],['adjacent energy',[one,0n,0n,one+1n,...a],0]];
 for(const state of [[0n,0n,0n,bits(2.5)],[sign,0n,0n,bits(2.5)],[one,0n,0n,one],[one,one+1n,0n,bits(2.5)],[one,0n,(one+1n)|sign,bits(2.5)],[1n,1n,1n,2n],[1n,0n,0n,one],[one,0n,0n,0x7fefffffffffffffn]]){
  cases.push(['bad left',[...state,...a],1],['bad right',[...a,...state],1]);
 }
 for(const special of [0x7ff0000000000000n,0xfff0000000000000n,0x7ff0000000000001n,0xfff0000000000001n,0x7ff8000000000000n,0xfff8000000000000n])for(let slot=0;slot<8;slot++){const q=[...a,...b];q[slot]=special;cases.push(['nonfinite slot'+slot,q,1]);}
 for(const [name,q,status]of cases){const expected=reference(q);assert.equal(expected[0],BigInt(status),'reference '+name);assert.deepEqual(callI64Slots(path.join(directory,'program.wasm'),'fluxCheckedBits',6,q),expected,name);}
 console.log('Checked '+cases.length+' 2D directional fluxes through Wasmtime, all raw words and opcode counts; retained '+directory);
}
main();
