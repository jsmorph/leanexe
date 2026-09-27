#!/usr/bin/env node
import fs from 'node:fs/promises';
import {parseArgs} from 'node:util';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {createWordGpu} from './word-gpu.mjs';

const {values}=parseArgs({options:{input:{type:'string'},example:{type:'boolean'},
  features:{type:'string',default:'4'},rows:{type:'string',default:'64'},
  denominator:{type:'string',default:'128'},backend:{type:'string',default:'cpu'},
  eta:{type:'string'},method:{type:'string',default:'auto'},fixture:{type:'string',default:'correlated'},
  diagnostics:{type:'boolean'},'allow-software':{type:'boolean'},help:{type:'boolean'}}});

function lean(input) {
  const run=spawnSync('tools/leanrun',['--timeout','5m','lake','-d','proofs/talos/lean',
    'env','lean','--run',fileURLToPath(new URL('word-estimator.lean',import.meta.url))],{
    cwd:fileURLToPath(new URL('../..',import.meta.url)),encoding:'utf8',maxBuffer:4*1024*1024,
    input:JSON.stringify(input)+'\n',
  });
  if(run.error) throw run.error;
  if(run.status!==0) throw new Error(`Lean exited with status ${run.status}${run.signal ? `, signal ${run.signal}`:''}:\n${(run.stderr+'\n'+run.stdout).trim()}`);
  return JSON.parse(run.stdout);
}

if(values.help) {
  console.log('Exact integer moments: --example [--features 1..32] [--rows count] [--fixture correlated|cancellation] or --input data.json [--denominator power-of-two] [--backend cpu|gpu] [--method auto|preconditioned] [--eta positive-ridge]. Every input must be exactly representable as a signed 16-bit integer divided by the denominator.');
} else try {
  if(Boolean(values.input)===Boolean(values.example)) throw new Error('Choose --input or --example');
  if(!['cpu','gpu'].includes(values.backend)) throw new Error('Backend must be cpu or gpu');
  if(!['auto','preconditioned'].includes(values.method)) throw new Error('Method must be auto or preconditioned');
  if(!['correlated','cancellation'].includes(values.fixture)) throw new Error('Unknown example fixture');
  const denominator=Number(values.denominator);
  if(!Number.isSafeInteger(denominator)||denominator<=0||
    (BigInt(denominator)&(BigInt(denominator)-1n))!==0n)
    throw new Error('Denominator must be a positive safe-integer power of two');
  let input;
  if(values.example) {
    const m=Number(values.features),n=Number(values.rows);
    if(!Number.isInteger(m)||m<1||m>32||!Number.isInteger(n)||n<1||(n+3)*m>524288)
      throw new Error('Invalid example shape');
    let state=271828183;
    const next=()=>{state^=state<<13;state^=state>>>17;state^=state<<5;return (state>>>0)%17-8;};
    const rows=(count,shift)=>Array.from({length:count},()=>{
      const common=next();
      return Array.from({length:m},(_,j)=>(next()+((j%3)-1)*common+shift*(j%2 ? -1:1))/128);
    });
    input={p:rows(n,2),q:rows(n+3,0),eta:1};
    if(values.fixture==='cancellation') {
      if(m!==2||n%2!==0) throw new Error('Cancellation fixture requires 2 features and an even row count');
      const q=Array.from({length:n},(_,i)=>[i%2 ? 4:-4,i%2 ? 4:-4]);
      input={p:q.map(([a,b])=>[a-1/4096,b+1/4096]),q,eta:2**-20};
    }
  } else input=JSON.parse(await fs.readFile(values.input,'utf8'));
  const m=input.p?.[0]?.length;
  if(!Number.isInteger(m)||m<1||m>32) throw new Error('Feature count must be between 1 and 32');
  const encodeRows=rows=>{
    if(!Array.isArray(rows)||!rows.length||rows.length*m>524288) throw new Error('Invalid sample count');
    return rows.map(row=>{
      if(!Array.isArray(row)||row.length!==m) throw new Error('Inconsistent feature count');
      return row.map(x=>{
        const integer=x*denominator;
        if(typeof x!=='number'||!Number.isFinite(x)||!Number.isInteger(integer)||integer< -32768||integer>32767)
          throw new Error('Observation is not exactly representable in the selected signed 16-bit format');
        return integer+32768;
      });
    });
  };
  const p=encodeRows(input.p),q=encodeRows(input.q),eta=values.eta===undefined ? (input.eta ?? 1):Number(values.eta);
  if(typeof eta!=='number'||!Number.isFinite(eta)||eta<=0) throw new Error('Ridge must be positive and finite');
  const word=new DataView(new ArrayBuffer(8));word.setFloat64(0,eta,true);
  const request={features:m,denominator,eta:word.getBigUint64(0,true).toString(),method:values.method};
  let result,adapter;
  if(values.backend==='cpu') result=lean({...request,mode:values.diagnostics ? 'cpu-diagnostics':'cpu',p,q});
  else {
    const {source}=lean({mode:'shader'});
    const gpu=await createWordGpu(source,{allowSoftware:values['allow-software']});
    try {
      const tp=await gpu.moments(p,m),tq=await gpu.moments(q,m);
      adapter=gpu.info;
      result=lean({...request,mode:values.diagnostics ? 'gpu-diagnostics':'gpu-finish',np:p.length,nq:q.length,tp,tq});
    } finally {gpu.destroy();}
  }
  if(values.diagnostics) {
    console.log(JSON.stringify({features:m,samples:{p:p.length,q:q.length},eta,denominator,
      backend:values.backend,...(adapter ? {adapter}:{}),diagnostics:result},null,2));
  } else {
    const z=BigInt(result.scaledScore),absolute=z<0n ? -z:z;
    const score=(z<0n ? '-':'')+(absolute/1000000000000n).toString()+'.'+
      (absolute%1000000000000n).toString().padStart(12,'0');
    console.log(JSON.stringify({score,absoluteErrorBound:result.absoluteErrorBound,
      features:m,samples:{p:p.length,q:q.length},eta,denominator,
      backend:values.backend,...(adapter ? {adapter}:{}),arithmetic:'exact u32 moment reductions; exact rational score',
      method:values.method,iterations:result.iterations,proof:result.proof},null,2));
  }
} catch(error) {
  console.error(`spectral-word-moments: ${error.message}`);process.exitCode=1;
}
