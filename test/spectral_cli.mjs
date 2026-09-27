import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import processes from '../tools/run-process.js';
import {referenceMoments,referenceScore} from '../tools/spectral-kl/reference.mjs';

const dir=await fs.mkdtemp(path.join(os.tmpdir(),'spectral-kl-'));
const input=path.join(dir,'input.json');
const command=(...args)=>{
  const result=spawnSync(process.execPath,['tools/spectral-kl.mjs',...args],
    {encoding:'utf8',timeout:90000});
  if (result.error) throw result.error;
  return result;
};
try {
  const p=[[0.1,0.3],[0.2,-0.4],[-0.1,0.5]],q=[[0,0.4],[0.3,-0.3]];
  await fs.writeFile(input,JSON.stringify({p,q,eta:1}));
  const result=command('--input',input);
  assert.equal(result.status,0,result.stderr);
  const output=JSON.parse(result.stdout);
  const expected=referenceScore(referenceMoments(Float32Array.from(p.flat()),2),
    referenceMoments(Float32Array.from(q.flat()),2),2,1);
  assert.ok(Math.abs(output.score-expected)<1e-12);
  assert.equal(output.backend,'cpu');
  assert.equal(output.features,2);
  assert.deepEqual(output.samples,{p:3,q:2});
  assert.equal(output.absoluteErrorBound,1e-6);
  const candidateData=JSON.parse(await fs.readFile(output.checkInput,'utf8'));
  const accepted=JSON.parse(await fs.readFile(path.join(path.dirname(output.checkInput),'result.json'),'utf8'));
  assert.equal(accepted.accepted,true);
  assert.equal(accepted.theorem,'Project.SpectralKL.Certificate.accepts_sound');
  const word=x=>{const b=Buffer.alloc(8);b.writeDoubleLE(x);return b.readBigUInt64LE().toString();};
  // Integration checks: corrupted proposals must fail closed. The universal
  // Lean theorem, rather than these examples, establishes numerical accuracy.
  for(const mutate of [
    c=>{c.score=word(1);},
    c=>{c.cells.at(-1).end=word(0.75);},
    c=>{c.cells[1].end=word(0);},
    c=>{c.cells=c.cells.map(v=>({...v,x:v.x.map(()=>word(0))}));},
    c=>{c.eta=word(0);},
    c=>{c.tolerance=word(-1);},
    c=>{c.p[0][0]=word(Infinity);},
  ]) {
    const corrupt=structuredClone(candidateData);mutate(corrupt);
    await fs.writeFile(input,JSON.stringify(corrupt));
    assert.throws(()=>processes.runChecked(['lake','--dir',path.resolve('proofs/talos/lean'),
      'env','lean','--run',path.resolve('tools/spectral-kl/check.lean'),input],
      {encoding:'utf8',timeout:90000}),/score rejected|nonfinite/);
  }
  for(const invalid of [
    {p:[[1,2]],q:[[1]]},
    {p:[['1']],q:[[0]]},
    {p:[[1]],q:[[0]],eta:0},
    {p:[[2]],q:[[0]],eta:1}, // Spectrum outside the admitted interval.
  ]) {
    await fs.writeFile(input,JSON.stringify(invalid));
    const rejected=command('--input',input);
    assert.equal(rejected.status,1);
    assert.match(rejected.stderr,/^spectral-kl:/);
    assert.equal(rejected.stdout,'');
  }
  const usage=command('--backend','unknown','--example');
  assert.equal(usage.status,1);
  assert.match(usage.stderr,/Backend must/);
  if(process.argv.includes('--gpu')) {
    const gpuArgs=['--backend','gpu',...(process.argv.includes('--allow-software')?['--allow-software']:[])];
    await fs.writeFile(input,JSON.stringify({p,q,eta:1}));
    const goodGpu=command('--input',input,...gpuArgs);
    assert.equal(goodGpu.status,0,goodGpu.stderr);
    assert.equal(JSON.parse(goodGpu.stdout).absoluteErrorBound,1e-6);
    // Nearly dependent features: binary32 Gram accumulation erases the
    // weak direction, making the formerly accepted GPU score about 6% wrong.
    const cq=Array.from({length:512},(_,i)=>[i%2?4:-4,i%2?4:-4]);
    const cp=cq.map(([a,b])=>[a-0.0003,b+0.0003]);
    await fs.writeFile(input,JSON.stringify({p:cp,q:cq,eta:2**-20}));
    const badGpu=command('--input',input,...gpuArgs);
    assert.equal(badGpu.status,1,badGpu.stdout);
    assert.equal(badGpu.stdout,'');
    assert.match(badGpu.stderr,/score rejected/);
    const goodCpu=command('--input',input,'--intervals','128');
    assert.equal(goodCpu.status,0,goodCpu.stderr);
    assert.equal(JSON.parse(goodCpu.stdout).absoluteErrorBound,1e-6);
    console.log('Spectral CLI: GPU score accepted; ill-conditioned GPU proposal rejected; CPU score accepted');
  }
  console.log('Spectral CLI: proved acceptance path, metadata and invalid numerical inputs passed');
} finally {await fs.rm(dir,{recursive:true,force:true});}
