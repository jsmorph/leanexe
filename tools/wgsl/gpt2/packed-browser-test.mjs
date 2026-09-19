#!/usr/bin/env node
// Execute the real browser host/worker under Node worker bindings. This is not a
// browser/WebGPU conformance test. The CPU path must work with those APIs absent.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import {Worker as NodeWorker} from 'node:worker_threads';
import {pathToFileURL} from 'node:url';
const [bundleArg,traceArg,outputArg]=process.argv.slice(2);
const nativeSharedArrayBuffer=globalThis.SharedArrayBuffer;
assert(bundleArg&&traceArg&&outputArg,'usage: packed-browser-test.mjs BUNDLE SCIENCE_TRACE FRESH_OUTPUT');
const bundle=path.resolve(bundleArg),expected=fs.readFileSync(traceArg),output=path.resolve(outputArg);
assert(!fs.existsSync(output),'output must be fresh');fs.mkdirSync(output,{recursive:true});
const bootstrap=`
const {parentPort,workerData}=require('node:worker_threads');
const fs=require('node:fs/promises'),path=require('node:path');
globalThis.SharedArrayBuffer=undefined;
globalThis.self={postMessage:(data,transfer)=>parentPort.postMessage(data,transfer)};
globalThis.fetch=async url=>{
  const name=String(url).replace('/bundle/','');
  if(!['model-cpu.wasm','tokenizer.wasm','sampler.wasm','transfer.wasm','tokenizer.bin','weights.bin'].includes(name))throw Error('Unexpected CPU fetch: '+name);
  parentPort.postMessage({type:'test-fetch',name});
  return {ok:true,arrayBuffer:async()=>{const b=await fs.readFile(path.join(workerData.bundle,name));return b.byteOffset===0&&b.byteLength===b.buffer.byteLength?b.buffer:b.buffer.slice(b.byteOffset,b.byteOffset+b.byteLength);}};
};
import(workerData.url).then(()=>parentPort.on('message',data=>self.onmessage({data})));
`;
let active=0;const requests=[];
globalThis.Worker=class {
  constructor(url){
    active++;this.worker=new NodeWorker(bootstrap,{eval:true,workerData:{bundle,url:String(url)}});
    this.worker.on('message',data=>{if(data.type==='test-fetch')requests.push(data.name);else this.onmessage?.({data});});
    this.worker.on('error',error=>this.onerror?.({message:error.message}));
  }
  postMessage(data){this.worker.postMessage(data);}
  terminate(){active--;return this.worker.terminate();}
};
Object.defineProperty(globalThis,'navigator',{value:{get gpu(){throw Error('CPU path accessed WebGPU');}},configurable:true});
globalThis.SharedArrayBuffer=undefined;globalThis.crossOriginIsolated=false;
const {runPacked}=await import(new URL('./packed-browser/host.js',import.meta.url));
const options={backend:'wasm',prompt:'The purpose of science is',generate:16,temperature:'0',seed:'42',trace:true};
let offset=0,text=options.prompt;const decoder=new TextDecoder(),tokens=[],events=[];
const result=await runPacked(options,event=>{
  if(event.type==='trace'){
    assert.equal(event.token,Number(expected.readBigUInt64LE(offset)));offset+=8;
    assert.deepEqual(Buffer.from(event.logits),expected.subarray(offset,offset+201028));offset+=201028;
  }
  if(event.type==='token'){tokens.push(event.token);text+=decoder.decode(event.bytes,{stream:true});}
  if(event.type==='stats')events.push(event.stats);
});
text+=decoder.decode();assert.equal(offset,expected.length);assert.equal(tokens.length,16);
assert.equal(result.dispatches,0);assert.equal(result.adapter,null);assert.equal(active,0);
assert.equal(result.stats.prefillCompleted,result.promptTokens);assert.equal(result.stats.decodeSteps,15);
assert.equal(result.stats.memory.gpuBufferBytes,0);assert.equal(result.stats.memory.sharedStagingBytes,0);
assert(result.stats.prefillMs>0&&result.stats.decodeMs>0&&result.stats.setupMs>0);
assert(result.stats.timeToFirstTokenMs>=result.stats.prefillMs);assert(result.stats.totalMs>=result.stats.setupMs+result.stats.prefillMs+result.stats.decodeMs);
for(let i=1;i<events.length;i++){
  assert(events[i].prefillMs>=events[i-1].prefillMs&&events[i].decodeMs>=events[i-1].decodeMs);
  assert(events[i].memory.modelWasmBytes>=events[i-1].memory.modelWasmBytes);
}
assert.deepEqual([...new Set(requests)].sort(),['model-cpu.wasm','sampler.wasm','tokenizer.bin','tokenizer.wasm','transfer.wasm','weights.bin'].sort());
const preAbort=new AbortController();preAbort.abort();
await assert.rejects(runPacked({...options,signal:preAbort.signal}),{name:'AbortError'});assert.equal(active,0);
const stop=new AbortController();
await assert.rejects(runPacked({...options,signal:stop.signal},event=>{if(event.type==='status')stop.abort();}),{name:'AbortError'});assert.equal(active,0);
const one=await runPacked({...options,generate:1,trace:false});
assert.equal(one.produced,1);assert.equal(one.stats.decodeSteps,0);assert.equal(one.stats.decodeMs,0);assert.equal(active,0);
const stopDecode=new AbortController();let emitted=0;
await assert.rejects(runPacked({...options,signal:stopDecode.signal},event=>{
  if(event.type==='token'){emitted++;stopDecode.abort();}
}),{name:'AbortError'});assert.equal(emitted,1);assert.equal(active,0);
await assert.rejects(runPacked({...options,backend:'unknown'}),/Unknown execution backend/);
// Failure-path test doubles: check partial GPU setup cleanup, without claiming
// these mocks execute or validate a shader.
globalThis.SharedArrayBuffer=nativeSharedArrayBuffer;globalThis.crossOriginIsolated=true;
globalThis.GPUBufferUsage={STORAGE:1,COPY_DST:2,COPY_SRC:4,MAP_READ:8};
let destroyed=0;
const device={destroy:()=>destroyed++,createBuffer:()=>({}),addEventListener:()=>{},lost:new Promise(()=>{}),
  createShaderModule:()=>({}),createComputePipelineAsync:async()=>{throw Error('test pipeline failure');}};
Object.defineProperty(globalThis,'navigator',{value:{gpu:{requestAdapter:async()=>({info:{isFallbackAdapter:true},requestDevice:async()=>device})}}});
globalThis.fetch=async()=>({ok:true,text:async()=>''});
await assert.rejects(runPacked({...options,backend:'wgsl'}),/test pipeline failure/);assert.equal(destroyed,1);assert.equal(active,0);
fs.writeFileSync(path.join(output,'result.json'),JSON.stringify({status:'pass',environment:'Node worker bindings; no browser execution',
  comparedLogits:16*50257,tokenIds:tokens,text,result,oneTokenStats:one.stats,requests,
  cancellation:'pre-start, loading and token emission passed',gpuSetupFailureCleanup:'test double passed'},null,2)+'\n');
console.log(JSON.stringify({status:'pass',text,stats:result.stats,output},null,2));
