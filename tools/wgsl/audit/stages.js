"use strict";
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),crypto=require('node:crypto');
const {root,cases}=require('./cases'),{model,word}=require('./model'),{arithmetic}=require('./real');
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const retained=JSON.parse(fs.readFileSync(path.join(root,'test/wgsl/numerical-audit/lean-traces.json'),'utf8'));
assert.equal(retained.traceSourceSha256,sha(fs.readFileSync(path.join(root,'tools/wgsl/audit/Trace.lean'))));
const results=cases().map(input=>{
  const real=arithmetic(120,input.weights),actual=model(input.weights).forward(input.tokens),ideal=real.forward(input.tokens);
  const lean=retained.results.find(x=>x.name===input.name);assert(lean);assert.deepEqual(lean.tokens,input.tokens);
  assert.equal(lean.weightsSha256,sha(input.weights));
  const convert=x=>Array.isArray(x)?x.map(convert):real.fromWord(word(x));
  const computed=Object.fromEntries(Object.entries(actual).map(([k,v])=>[k,convert(v)]));
  const stages=real.stageNames.map(name=>{
    assert.deepEqual(actual[name].flat().map(word),lean.trace[name],`${input.name}/${name}`);
    const fresh=real.stage(name,computed,input.tokens);
    return {name,localError:real.maxError(computed[name].flat(),fresh.flat()),
      totalError:real.maxError(computed[name].flat(),ideal.trace[name].flat()),
      computedMagnitude:Math.max(...actual[name].flat().map(Math.abs)),
      idealMagnitude:Math.max(...ideal.trace[name].flat().map(x=>Math.abs(real.number(x))))};
  });
  const q=ideal.logits.map(real.number),sorted=q.slice().sort((a,b)=>b-a);
  return {name:input.name,stages,denominators:ideal.denominators,logitRange:[Math.min(...q),Math.max(...q)],topTwoGap:sorted[0]-sorted[1]};
});
console.log(JSON.stringify({schemaVersion:1,status:'pass',scope:'finite-case diagnostic; local error uses computed predecessors, total error uses the ideal complete model',
 referenceDecimalPlaces:120,checks:{cases:results.length,leanWords:retained.results.reduce((n,x)=>n+Object.values(x.trace).reduce((s,a)=>s+a.length,0),0)},results},null,2));
