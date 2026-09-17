"use strict";
// Sequential runner-only evaluation of the existing Lean integer FP model.
const fs=require('node:fs'),path=require('node:path'),crypto=require('node:crypto'),assert=require('node:assert/strict');
const {spawnSync}=require('node:child_process');
const {root,cases}=require('./cases'),{model,word}=require('./model');
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const scratch=path.join(root,'build/wgsl/numerical-audit');fs.mkdirSync(scratch,{recursive:true});
const toolchain=process.env.LEANRUN_TOOLCHAIN || path.join(root,'build/tools/lean-4.34.0-rc2-darwin_aarch64');
const results=[];
for(const input of cases()){
  const inputFile=path.join(scratch,`${input.name}-weights.json`);
  fs.writeFileSync(inputFile,JSON.stringify(Array.from({length:2488},(_,i)=>input.weights.readBigUInt64LE(8*i).toString()))+'\n');
  const args=['--timeout','90s','--lock-timeout','10','--toolchain',toolchain,'lake','-d','proofs/talos/lean','env','lean','--run',
    'tools/wgsl/audit/Trace.lean',inputFile,...input.tokens.map(String)];
  const run=spawnSync(path.join(root,'tools/leanrun'),args,{cwd:root,env:process.env,encoding:'utf8',maxBuffer:4*1024*1024});
  fs.writeFileSync(path.join(scratch,`${input.name}-lean.log`),run.stderr+run.stdout);
  assert.equal(run.status,0,`${input.name}: ${run.error || run.stderr}\n${run.stdout}`);
  const trace=JSON.parse(run.stdout),js=model(input.weights).forward(input.tokens);
  for(const [stage,value] of Object.entries(js))assert.deepEqual(trace[stage],value.flat().map(word),`${input.name}/${stage}`);
  results.push({name:input.name,tokens:input.tokens,weightsSha256:sha(input.weights),trace});
  console.error(`${input.name}: ${Object.values(trace).reduce((n,v)=>n+v.length,0)} words match Lean`);
}
const output={schemaVersion:1,status:'pass',scope:'finite-case evaluation of the existing Lean FP model; not a new universal theorem',
  traceSourceSha256:sha(fs.readFileSync(path.join(root,'tools/wgsl/audit/Trace.lean'))),
  leanToolchain:fs.readFileSync(path.join(root,'proofs/talos/lean/lean-toolchain'),'utf8').trim(),results};
fs.writeFileSync(path.join(root,'test/wgsl/numerical-audit/lean-traces.json'),JSON.stringify(output,null,2)+'\n');
