#!/usr/bin/env node
import fs from 'node:fs/promises';
import {parseArgs} from 'node:util';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';

const {values}=parseArgs({options:{input:{type:'string'},example:{type:'boolean'},
  features:{type:'string',default:'4'},rows:{type:'string',default:'64'},
  scale:{type:'string',default:'1'},eta:{type:'string'},method:{type:'string',default:'auto'},help:{type:'boolean'}}});
if(values.help) {
  console.log('Matrix series estimator: --example [--features 1..32] [--rows count] [--scale number] or --input data.json [--method preconditioned|auto|damped|adaptive|fixed] [--eta positive-ridge]\nInput: {"p":[[number,...],...],"q":[[number,...],...],"eta":1}. Runs the proved rational computation directly in Lean.');
} else {
  try {
    if(Boolean(values.input)===Boolean(values.example)) throw new Error('Choose --input or --example');
    if(!['preconditioned','auto','damped','adaptive','fixed'].includes(values.method)) throw new Error('Method must be preconditioned, auto, damped, adaptive, or fixed');
    let input;
    if(values.example) {
      const m=Number(values.features), n=Number(values.rows), scale=Number(values.scale);
      if(!Number.isInteger(m)||m<1||m>32||!Number.isInteger(n)||n<1||(n+3)*m>524288)
        throw new Error('Invalid example shape');
      if(!Number.isFinite(scale)||scale<=0) throw new Error('Example scale must be positive and finite');
      let state=271828183;
      const next=()=>{
        state^=state<<13;state^=state>>>17;state^=state<<5;
        return (state>>>0)%17-8;
      };
      const rows=(count,shift)=>Array.from({length:count},()=>{
        const common=next();
        return Array.from({length:m},(_,j)=>scale*(next()+((j%3)-1)*common+shift*(j%2 ? -1:1))/128);
      });
      input={p:rows(n,2),q:rows(n+3,0),eta:1};
    } else input=JSON.parse(await fs.readFile(values.input,'utf8'));
    const m=input.p?.[0]?.length;
    if(!Number.isInteger(m)||m<1||m>32) throw new Error('Feature count must be between 1 and 32');
    for(const rows of [input.p,input.q]) {
      if(!Array.isArray(rows)||!rows.length||rows.length*m>524288||
        rows.some(row=>!Array.isArray(row)||row.length!==m||row.some(x=>typeof x!=='number'||!Number.isFinite(x))))
        throw new Error('Expected nonempty rectangular finite observations, at most 524288 values per group');
    }
    const eta=values.eta===undefined ? (input.eta ?? 1):Number(values.eta);
    if(typeof eta!=='number'||!Number.isFinite(eta)||eta<=0) throw new Error('Ridge must be positive and finite');
    const view=new DataView(new ArrayBuffer(8));
    const encode=x=>{view.setFloat64(0,x,true);return view.getBigUint64(0,true).toString();};
    const run=spawnSync('tools/leanrun',['--timeout','5m','lake','-d','proofs/talos/lean',
      'env','lean','--run',fileURLToPath(new URL('matrix-series.lean',import.meta.url))],{
      cwd:fileURLToPath(new URL('../..',import.meta.url)),encoding:'utf8',maxBuffer:1024*1024,
      input:JSON.stringify({features:m,p:input.p.map(row=>row.map(encode)),q:input.q.map(row=>row.map(encode)),eta:encode(eta),method:values.method})+'\n',
    });
    if(run.error) throw run.error;
    if(run.status!==0) throw new Error(`Lean exited with status ${run.status}${run.signal ? `, signal ${run.signal}`:''}:\n${(run.stderr+'\n'+run.stdout).trim()}`);
    const result=JSON.parse(run.stdout);
    const z=BigInt(result.scaledScore), absolute=z<0n ? -z:z;
    const score=(z<0n ? '-':'')+(absolute/1000000000000n).toString()+'.'+
      (absolute%1000000000000n).toString().padStart(12,'0');
    console.log(JSON.stringify({score,absoluteErrorBound:result.absoluteErrorBound,
      samples:{p:input.p.length,q:input.q.length},features:m,eta,
      arithmetic:'exact rational; score rounded to 12 decimal places',
      method:values.method,iterations:result.iterations,
      proof:result.proof},null,2));
  } catch(error) {
    console.error(`spectral-matrix-series: ${error.message}`);
    process.exitCode=1;
  }
}
