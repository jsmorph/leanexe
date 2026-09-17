"use strict";
const assert=require('node:assert/strict');
const {expNeg,gelu,word,fromWord}=require('./model'),{arithmetic}=require('./real');
const a=arithmetic(120,Buffer.alloc(2488*8));
const adjacent=x=>[fromWord(BigInt(word(x))-1n),x,fromWord(BigInt(word(x))+1n)];
function probe(name,fn,reference,inputs){
  const results=inputs.map(x=>{
    const ideal=reference(a.fromWord(word(x))),y=fn(x),error=a.maxError([a.fromWord(word(y))],[ideal]);
    const bound=name==='expNeg'?4029*2**-52*a.number(ideal)+Math.exp(-64):200000*2**-52;
    assert(error<=bound,`${name}(${x})`);return {x,result:y,error,existingBound:bound};
  });
  return {name,results,maxError:Math.max(...results.map(x=>x.error))};
}
const results=[probe('expNeg',expNeg,a.exp,[0,-(2**-55),...adjacent(-1),-2,-32,...adjacent(-64)]),
 probe('gelu',gelu,a.gelu,[-0,0,-(2**-55),2**-55,-0.001,0.001,-0.25,0.25,-1,1,-4,4,...adjacent(-8),...adjacent(8)])];
console.log(JSON.stringify({schemaVersion:1,status:'pass',scope:'boundary diagnostics against a 120-place reference; not exhaustive or interval-certified',results},null,2));
