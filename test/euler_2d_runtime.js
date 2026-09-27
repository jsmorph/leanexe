#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),assert=require('node:assert/strict'),path=require('node:path');
async function main(){
 const {run2D,verifyEvents,verifyEventStream,readEvents}=await import('../tools/euler-2d-runtime.mjs');
 for(const scenario of ['four-quadrants','circular-blast','riemann']){
  const run=run2D(8,5,scenario);
  const events=fs.readFileSync(path.join(run.evidenceDirectory,'run.ndjson'),'utf8').trim().split('\n').map(JSON.parse);
  const expected=verifyEvents(events),bytes=Buffer.from(events.map(JSON.stringify).join('\n'));
  async function* fragments(){for(let i=0;i<bytes.length;i+=127)yield bytes.subarray(i,i+127);}
  assert.deepEqual(await verifyEventStream(readEvents(fragments()),{retainFrames:true}),expected);
  assert.deepEqual(await verifyEventStream(events),{...expected,frames:[expected.frames.at(-1)]});
  const flip=s=>(BigInt('0x'+s)^1n).toString(16).padStart(16,'0');
  const corruptions=[
   es=>{es.find(e=>e.kind==='step').dt=flip(es.find(e=>e.kind==='step').dt);},
   es=>{es.find(e=>e.kind==='step').diagnostics[0]=flip(es.find(e=>e.kind==='step').diagnostics[0]);},
   es=>{es.find(e=>e.kind==='frame').densityPressureWords[0]=flip(es.find(e=>e.kind==='frame').densityPressureWords[0]);},
   es=>{es.at(-1).gridWords[0]=flip(es.at(-1).gridWords[0]);},
   es=>{es.at(-1).calls[0]++;},
   es=>{es.pop();},
   es=>{es.push(es.at(-1));},
   es=>{const frames=es.filter(e=>e.kind==='frame'),last=frames.at(-1),previous=frames.at(-2);es.splice(es.indexOf(last),1);es.splice(es.indexOf(previous)+1,0,{...structuredClone(previous),index:last.index});},
  ];
  for(const corrupt of corruptions){const changed=structuredClone(events);corrupt(changed);assert.throws(()=>verifyEvents(changed));await assert.rejects(()=>verifyEventStream(changed));}
  async function* brokenSource(){yield bytes.subarray(0,10);throw new Error('read failed');}
  await assert.rejects(()=>verifyEventStream(readEvents(brokenSource())),/read failed/);
  console.log(scenario+': native, in-memory, and streamed comparisons; '+corruptions.length+' corrupted-record rejections and read-error propagation; retained '+run.evidenceDirectory);
 }
 async function* oversized(){const chunk=Buffer.alloc(65536,32);for(let i=0;i<=1024;i++)yield chunk;}
 await assert.rejects(()=>verifyEventStream(readEvents(oversized())),/event exceeds 64 MiB/);
 console.log('Oversized event rejected before parsing');
}
main().catch(error=>{console.error(error.stack);process.exitCode=1;});
