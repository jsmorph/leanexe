import assert from 'node:assert/strict';
import fs from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import {spawnSync} from 'node:child_process';
import {referenceMoments,referenceScore} from '../tools/spectral-kl/reference.mjs';

const dir=await fs.mkdtemp(path.join(os.tmpdir(),'spectral-kl-'));
const input=path.join(dir,'input.json');
const command=(...args)=>{
  const result=spawnSync(process.execPath,['tools/spectral-kl.mjs',...args],
    {encoding:'utf8',timeout:30000});
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
  console.log('Spectral CLI: JSON input, independent score, metadata and rejection checks passed');
} finally {await fs.rm(dir,{recursive:true,force:true});}
