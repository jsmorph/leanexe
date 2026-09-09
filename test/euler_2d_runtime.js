#!/usr/bin/env node
'use strict';
const fs=require('node:fs'),assert=require('node:assert/strict'),path=require('node:path');
async function main(){
 const {run2D,verifyEvents}=await import('../tools/euler-2d-runtime.mjs');
 for(const scenario of ['four-quadrants','circular-blast']){
  const run=run2D(8,5,scenario);
  const events=fs.readFileSync(path.join(run.evidenceDirectory,'run.ndjson'),'utf8').trim().split('\n').map(JSON.parse);
  const flip=s=>(BigInt('0x'+s)^1n).toString(16).padStart(16,'0');
  const corruptions=[
   es=>{es.find(e=>e.kind==='step').dt=flip(es.find(e=>e.kind==='step').dt);},
   es=>{es.find(e=>e.kind==='step').diagnostics[0]=flip(es.find(e=>e.kind==='step').diagnostics[0]);},
   es=>{es.find(e=>e.kind==='frame').densityPressureWords[0]=flip(es.find(e=>e.kind==='frame').densityPressureWords[0]);},
   es=>{es.at(-1).gridWords[0]=flip(es.at(-1).gridWords[0]);},
   es=>{es.at(-1).calls[0]++;},
   es=>{es.pop();},
  ];
  for(const corrupt of corruptions){const changed=structuredClone(events);corrupt(changed);assert.throws(()=>verifyEvents(changed));}
  console.log(scenario+': full native/oracle comparison and six corrupted-record rejections; retained '+run.evidenceDirectory);
 }
}
main().catch(error=>{console.error(error.stack);process.exitCode=1;});
