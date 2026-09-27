import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import {CpuEstimator} from '../tools/spectral-kl/runtime.mjs';
import {referenceMoments,referenceScore,observations} from '../tools/spectral-kl/reference.mjs';

const cpu=await CpuEstimator.create(await fs.readFile('.lake/build/spectral-kl/matrix.wasm'));
function maxDifference(a,b) {
  assert.equal(a.length,b.length);
  return a.reduce((d,x,i)=>Math.max(d,Math.abs(x-b[i])),0);
}
const cases=[];
for(const m of [1,2,3,8,16,32]) {
  const n=m===32?16381:257;
  const p=observations(n,m,42,0.15),q=observations(n+3>524288/m?n:n+3,m,91);
  const pm=cpu.moments(p,m),qm=cpu.moments(q,m);
  assert.ok(maxDifference(pm,referenceMoments(p,m))<2e-14);
  assert.ok(maxDifference(qm,referenceMoments(q,m))<2e-14);
  const score=cpu.score(pm,qm,m,1), reference=referenceScore(pm,qm,m,1);
  assert.ok(Math.abs(score-reference)<2e-11,`m=${m}: score ${score}, reference ${reference}`);
  assert.equal(cpu.score(pm,pm,m,1),0);
  assert.ok(cpu.score(pm,qm,m,2)<=score+1e-14);
  const permute=rows=>Float32Array.from(rows,(_,index)=>-rows[Math.floor(index/m)*m+(m-1-index%m)]);
  const transformed=cpu.estimate(permute(p),permute(q),m,1);
  assert.ok(Math.abs(transformed-score)<2e-11,`orthogonal feature change m=${m}`);
  cases.push({p,q,m,pm,qm,score});
  console.log(`CPU m=${m} n=${n}: score=${score}, independent quadrature error=${Math.abs(score-reference)}`);
}
// Repeated features make raw second moments rank deficient; ridge must handle them.
const duplicate=Float32Array.from([1,1,-1,-1,0.5,0.5]);
const zero=new Float32Array(duplicate.length);
const dm=cpu.moments(duplicate,2), zm=cpu.moments(zero,2);
assert.ok(Math.abs(cpu.score(dm,zm,2,4)-referenceScore(dm,zm,2,4))<2e-11);
// Equal non-diagonal second moments produce repeated eigenvalues at one.
// A nonzero mean difference checks the transformed coordinates and h(1).
const equalP=[0.2,-0.1,1,0.3,0.3,0.5],equalQ=[0,0,1,0.3,0.3,0.5];
assert.ok(Math.abs(cpu.score(equalP,equalQ,2,0.25)-referenceScore(equalP,equalQ,2,0.25))<2e-14);
// Largest allowed feature magnitude, rank-one moments and minimum ridge.
// Sherman–Morrison gives this independent closed form; condition numbers
// reach roughly 8.6e9, so the test also exercises delicate whitening.
const illConditioned=[];
for(const m of [2,8,32]) {
  const p=new Float32Array(m).fill(16),q=new Float32Array(m).fill(-16),eta=2**-20;
  const expected=512*m/(eta+256*m);
  assert.ok(Math.abs(cpu.estimate(p,q,m,eta)-expected)<2e-12,`minimum ridge m=${m}`);
  illConditioned.push({p,q,m,eta,expected});
}
assert.throws(()=>cpu.moments(new Float32Array(),2));
assert.throws(()=>cpu.moments(new Float32Array([NaN]),1));
assert.throws(()=>cpu.moments(new Float32Array([17]),1));
assert.throws(()=>cpu.moments(new Float32Array([1,2,3]),2));
assert.throws(()=>cpu.score([0,1],[0,0],1,0.25),/spectrum/);
assert.throws(()=>cpu.score([0,0,1,0,0,1],[0,0,1,2,2,1],2,0.25),/Cholesky/);
assert.throws(()=>cpu.score([0,0,1,0.2,0,1],[0,0,1,0,0,1],2,1),/invalid/);
console.log('CPU matrix checks: dimensions, direct quadrature, zero, ridge monotonicity, orthogonal invariance, rank deficiency and rejection passed');

if(process.argv.includes('--gpu')) {
  const {createNodeGpu}=await import('../tools/spectral-kl/node-gpu.mjs');
  const gpu=await createNodeGpu({allowSoftware:process.argv.includes('--allow-software')});
  try {
    console.log(`WebGPU adapter: ${JSON.stringify(gpu.info)}`);
    for(const {p,q,m,pm,qm,score} of cases) {
      const pg=await gpu.moments(p,m),qg=await gpu.moments(q,m);
      const momentError=Math.max(maxDifference(pg,pm),maxDifference(qg,qm));
      assert.ok(momentError<2e-6,`WebGPU moments m=${m}: ${momentError}`);
      const gpuScore=cpu.score(pg,qg,m,1);
      assert.ok(Math.abs(gpuScore-score)<2e-6,`GPU end-to-end m=${m}`);
      console.log(`GPU m=${m}: moment difference=${momentError}, score difference=${Math.abs(gpuScore-score)}`);
    }
    for(const n of [1,255,256,257,1031]) {
      const input=Float32Array.from({length:n*3},(_,i)=>i%2?16:-16);
      const expected=cpu.moments(input,3),actual=await gpu.moments(input,3);
      assert.ok(maxDifference(expected,actual)<2e-5,`partial tile n=${n}`);
    }
    for(const {p,q,m,eta,expected} of illConditioned) {
      const score=cpu.score(await gpu.moments(p,m),await gpu.moments(q,m),m,eta);
      assert.ok(Math.abs(score-expected)<2e-12,`WebGPU minimum ridge m=${m}`);
    }
    await assert.rejects(()=>gpu.moments(new Float32Array([Infinity]),1));
    console.log('WebGPU full pipeline and tile-boundary checks passed');
  } finally {gpu.destroy();}
}
