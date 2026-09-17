"use strict";
const fs=require("node:fs"),path=require("node:path"),crypto=require("node:crypto"),assert=require("node:assert/strict");
const {root,cases}=require("./cases"),{model,word,fromWord}=require("./model"),{arithmetic}=require("./real");
const digest=x=>crypto.createHash("sha256").update(x).digest("hex");
const wasm=fs.readFileSync(path.join(root,"test/wgsl/gpt/hidden.wasm"));
assert.equal(digest(wasm),"d03534266e4171a07512566429763ba890506ba306a6073379d2433b395837a2");
const module_=new WebAssembly.Module(wasm),held=[];
function visit(x){if(!x||typeof x!=="object")return;if(Array.isArray(x.logits)&&Array.isArray(x.tokens)){held.push(x);return;}for(const v of Object.values(x))visit(v);}
visit(JSON.parse(fs.readFileSync(path.join(root,"test/wgsl/gpt/evidence.json"),"utf8")));
const results=cases().map(input=>{
  const machine=model(input.weights),trace=machine.forward(input.tokens);
  assert(machine.w.every(x=>Number.isFinite(x)&&Math.abs(x)<=4));
  const instance=new WebAssembly.Instance(module_,{}),memory=instance.exports.memory.buffer;
  new DataView(memory).setBigUint64(256,2488n,true);new Uint8Array(memory,264,input.weights.length).set(input.weights);
  const before=Buffer.from(memory),native=instance.exports.hidden(256n,...input.tokens.map(BigInt),3n).map(x=>BigInt.asUintN(64,x).toString());
  assert(Buffer.from(memory).equals(before));assert.deepEqual(trace.hidden.map(word),native);
  if(input.name.startsWith("checkpoint")){
    const prior=held.find(x=>JSON.stringify(x.tokens)===JSON.stringify(input.tokens));assert(prior);
    assert.equal(prior.weightsSha256,digest(input.weights));assert.equal(prior.hiddenSha256,digest(wasm));
    assert.deepEqual(trace.mixed.map(word),prior.logits);
  }else assert(native.every(x=>BigInt(x)===0n));
  const low=arithmetic(80,input.weights),high=arithmetic(120,input.weights);
  const a=low.forward(input.tokens),b=high.forward(input.tokens);
  const precisionDifference=high.maxError(a.logits.map(x=>x*10n**40n),b.logits);
  assert(precisionDifference<1e-55);
  const hiddenError=high.maxError(native.map(high.fromWord),b.hidden);
  const mixedError=high.maxError(trace.mixed.map(x=>high.fromWord(word(x))),b.logits);
  if(input.name.endsWith("plus"))assert(b.logits[0]>59n*high.S);
  if(input.name.endsWith("minus"))assert(b.logits[0]<-59n*high.S);
  return {name:input.name,tokens:input.tokens,weightsSha256:digest(input.weights),nativeHidden:native.map(fromWord),
    idealEvenLogit:high.number(b.logits[0]),precisionDifference,hiddenError,mixedError,denominators:b.denominators};
});
console.log(JSON.stringify({schemaVersion:1,status:"pass",scope:"diagnostic evidence, not a new formal theorem",wasmSha256:digest(wasm),
  checks:{cases:results.length,checkpointNativeLogits:768,hiddenWords:24,referenceDecimalPlaces:[80,120]},results},null,2));
