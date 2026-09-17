"use strict";
// Focused diagnostics; never rebuilds artifacts or invokes Lean.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {spawnSync}=require('node:child_process'),{root}=require('./cases');
for(const name of ['baseline','stages','sensitivity','alternatives','scalars','bounds']){
  const run=spawnSync(process.execPath,[path.join(__dirname,`${name}.js`)],{cwd:root,encoding:'utf8',maxBuffer:4*1024*1024});
  assert.equal(run.status,0,`${name}: ${run.error||run.stderr}\n${run.stdout}`);
  const actual=JSON.parse(run.stdout),expected=JSON.parse(fs.readFileSync(path.join(root,`test/wgsl/numerical-audit/${name}.json`),'utf8'));
  assert.deepEqual(actual,expected,`${name}: retained diagnostic changed; inspect before updating evidence`);
  console.log(`${name}: pass`);
}
const exact=spawnSync(process.execPath,[path.join(__dirname,'inequalities.js')],{cwd:root,encoding:'utf8'});
assert.equal(exact.status,0,exact.stderr);console.log('27 exact rational comparisons: pass');
