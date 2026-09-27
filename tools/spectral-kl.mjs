#!/usr/bin/env node
import fs from 'node:fs/promises';
import {parseArgs} from 'node:util';
import {CpuEstimator,validateFeatures} from './spectral-kl/runtime.mjs';
import {observations} from './spectral-kl/reference.mjs';

const help=`Spectral KL moment estimator

  node tools/spectral-kl.mjs --example [--backend cpu|gpu]
  node tools/spectral-kl.mjs --input observations.json [--backend cpu|gpu]

Input: {"p": [[feature, ...], ...], "q": [[feature, ...], ...], "eta": 1}
Both groups use the same 1–32 features, with at most 524288 values per group.
Values must be finite and in [-16,16]. Inputs are rounded to binary32 for both
backends. eta defaults to 1 and must be in [2^-20,256]. The current solver
accepts generalized eigenvalues in [1/2,3/2].

Build first: node tools/spectral-kl/build.js
GPU dependency: npm install --prefix build/spectral-kl-gpu webgpu@0.6.1
--allow-software permits a software WebGPU adapter for validation.
`;

function features(rows,width) {
  if (!Array.isArray(rows) || !rows.length || rows.length*width>524288) {
    throw new Error('Each group must be a nonempty array of rows, at most 524288 values');
  }
  const out=new Float32Array(rows.length*width);
  for(let r=0;r<rows.length;r++) {
    if (!Array.isArray(rows[r]) || rows[r].length!==width) throw new Error('All rows must have the same feature count');
    for(let j=0;j<width;j++) {
      const x=rows[r][j];
      if (typeof x!=='number' || !Number.isFinite(x) || Math.abs(x)>16) {
        throw new Error('Features must be numbers in [-16,16]');
      }
      out[r*width+j]=x;
    }
  }
  validateFeatures(out,width);
  return out;
}

async function main() {
  const {values}=parseArgs({options:{
    help:{type:'boolean'},example:{type:'boolean'},input:{type:'string'},
    backend:{type:'string',default:'cpu'},'allow-software':{type:'boolean'},
  }});
  if (values.help) {console.log(help);return;}
  if (!['cpu','gpu'].includes(values.backend)) throw new Error('Backend must be cpu or gpu');
  if (Boolean(values.example)===Boolean(values.input)) throw new Error('Choose --input or --example');
  let p,q,width,eta;
  if (values.example) {
    width=32;eta=1;
    p=observations(16381,width,42,0.15);q=observations(16384,width,91);
  } else {
    const input=JSON.parse(await fs.readFile(values.input,'utf8'));
    width=input?.p?.[0]?.length;
    if (!Number.isInteger(width) || width<1 || width>32) throw new Error('Expected 1–32 features per row');
    p=features(input.p,width);q=features(input.q,width);eta=input.eta ?? 1;
  }
  if (typeof eta!=='number' || !Number.isFinite(eta) || eta<2**-20 || eta>256) {
    throw new Error('Regularization eta must be a number in [2^-20,256]');
  }
  const bytes=await fs.readFile(new URL('../.lake/build/spectral-kl/matrix.wasm',import.meta.url));
  const cpu=await CpuEstimator.create(bytes);
  let gpu;
  try {
    let pm,qm;
    if (values.backend==='gpu') {
      const {createNodeGpu}=await import('./spectral-kl/node-gpu.mjs');
      gpu=await createNodeGpu({allowSoftware:values['allow-software']});
      pm=await gpu.moments(p,width);qm=await gpu.moments(q,width);
    } else {pm=cpu.moments(p,width);qm=cpu.moments(q,width);}
    const score=cpu.score(pm,qm,width,eta);
    console.log(JSON.stringify({score,backend:values.backend,features:width,
      samples:{p:p.length/width,q:q.length/width},eta,inputPrecision:'binary32',
      momentPrecision:gpu?'binary32':'binary64',solver:'Lean/WASM binary64',
      ...(gpu?{adapter:gpu.info}:{}),
    },null,2));
  } finally {gpu?.destroy();}
}

try {await main();} catch(error) {
  console.error(`spectral-kl: ${error.message}`);
  process.exitCode=1;
}
