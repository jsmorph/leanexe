#!/usr/bin/env node
import fs from 'node:fs/promises';
import {parseArgs} from 'node:util';
import {spawnSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';

const {values}=parseArgs({options:{input:{type:'string'},example:{type:'boolean'},
  engine:{type:'string',default:'lean'},eta:{type:'string'},help:{type:'boolean'}}});
if(values.help) {
  console.log('Scalar spectral estimator: --example or --input data.json [--engine lean|wasm] [--eta number]\nInput: {"p":[number,...],"q":[number,...],"eta":1}; each group has 1–1048576 samples in [-0.5,0.5]. Ridge: [1,256], default 1. Default engine: direct Lean.');
} else {
  try {
    if(Boolean(values.input)===Boolean(values.example)) throw new Error('Choose --input or --example');
    const input=values.example ? {
      p:Array.from({length:65536},(_,i)=>0.1+0.3*Math.sin(i*0.13)),
      q:Array.from({length:65539},(_,i)=>0.25*Math.cos(i*0.17)),
    } : JSON.parse(await fs.readFile(values.input,'utf8'));
    for(const rows of [input.p,input.q]) {
      if(!Array.isArray(rows) || !rows.length || rows.length>1048576 ||
        rows.some(x=>typeof x!=='number' || !Number.isFinite(x) || Math.abs(x)>0.5)) {
        throw new Error('Expected 1–1048576 finite samples in [-0.5,0.5] per group');
      }
    }
    const eta=values.eta===undefined ? (input.eta ?? 1) : Number(values.eta);
    if(typeof eta!=='number' || !Number.isFinite(eta) || eta<1 || eta>256) {
      throw new Error('Ridge must be a finite number in [1,256]');
    }
    const bitsView=new DataView(new ArrayBuffer(8));
    const encode=x=>{
      bitsView.setFloat64(0,x,true);
      return bitsView.getBigUint64(0,true).toString();
    };
    let word;
    if(values.engine==='lean') {
      const root=fileURLToPath(new URL('../..',import.meta.url));
      const run=spawnSync('tools/leanrun',['--timeout','3m','lake','-d','proofs/talos/lean',
        'env','lean','--run',fileURLToPath(new URL('scalar.lean',import.meta.url))],{
        cwd:root,input:JSON.stringify({p:input.p.map(encode),q:input.q.map(encode),eta:encode(eta)})+'\n',
        encoding:'utf8',maxBuffer:1024*1024,
      });
      if(run.error) throw run.error;
      if(run.status!==0) throw new Error((run.stderr+'\n'+run.stdout).trim());
      word=BigInt(JSON.parse(run.stdout).bits);
    } else if(values.engine==='wasm') {
      const bytes=await fs.readFile(new URL('../../.lake/build/spectral-kl/spectral-kl.wasm',import.meta.url));
      const {instance}=await WebAssembly.instantiate(bytes,{});
      const e=instance.exports;
      const put=rows=>{
        const ptr=e.alloc(BigInt(8+8*rows.length));
        const view=new DataView(e.memory.buffer);
        view.setBigUint64(Number(ptr),BigInt(rows.length),true);
        rows.forEach((x,i)=>view.setFloat64(Number(ptr)+8+8*i,x,true));
        return ptr;
      };
      const [status,result]=e.fromBoundedSamples(put(input.p),put(input.q),BigInt(encode(eta)));
      if(status!==0n) throw new Error(`Estimator rejected the input (status ${status})`);
      word=result;
    } else throw new Error('Engine must be lean or wasm');
    const view=new DataView(new ArrayBuffer(8));
    view.setBigUint64(0,BigInt.asUintN(64,word),true);
    console.log(JSON.stringify({score:view.getFloat64(0,true),absoluteErrorBound:1e-6,
      samples:{p:input.p.length,q:input.q.length},eta,inputPrecision:'binary64',engine:values.engine,
      proof:'Project.SpectralKL.Scalar.fromBoundedSamples_correct'},null,2));
  } catch(error) {
    console.error(`spectral-scalar: ${error.message}`);
    process.exitCode=1;
  }
}
