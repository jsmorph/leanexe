"use strict";
// Pointwise central differences, not global bounds or rigorous intervals.
const assert=require('node:assert/strict');
const {cases}=require('./cases'),{arithmetic}=require('./real');
function estimate(input,stage,power){
  const a=arithmetic(100,input.weights),h=10n**BigInt(100-power),base=a.forward(input.tokens),value=base.trace[stage];
  const nested=Array.isArray(value[0]),flat=value.flat(),sums=Array(256).fill(0n);
  const abs=x=>x<0n?-x:x;
  for(let i=0;i<flat.length;i++){
    const run=sign=>a.forward(input.tokens,(name,x)=>{
      if(name!==stage)return x;
      const v=flat.slice();v[i]+=sign*h;
      return nested?value.map((row,j)=>v.slice(j*row.length,(j+1)*row.length)):v;
    }).logits;
    const plus=run(1n),minus=run(-1n);
    for(let j=0;j<256;j++)sums[j]+=abs((plus[j]-minus[j])*a.S/(2n*h));
  }
  return {fixedNorm:sums.reduce((x,y)=>x>y?x:y),scale:a.S};
}
const results=cases().filter(x=>x.name!=='checkpoint-zeros'&&x.name!=='checkpoint-byte-edges').map(input=>{
  const sensitivities=['embedding','scores','residual1','residual2','hidden'].map(stage=>{
    const coarse=estimate(input,stage,30),fine=estimate(input,stage,32);
    const delta=coarse.fixedNorm-fine.fixedNorm,den=fine.fixedNorm>fine.scale?fine.fixedNorm:fine.scale;
    const relativeDifference=Number(delta<0n?-delta:delta)/Number(den);
    assert(relativeDifference<1e-12,`${input.name}/${stage} step convergence`);
    return {stage,infinityToInfinityJacobianNorm:Number(fine.fixedNorm)/Number(fine.scale),relativeStepDifference:relativeDifference};
  });
  console.error(`${input.name}: finite differences converged`);
  return {name:input.name,sensitivities};
});
const checkpoint=cases()[0],r=arithmetic(100,checkpoint.weights);
console.log(JSON.stringify({schemaVersion:1,status:'pass',scope:'pointwise diagnostic at ideal real intermediates; no uniform upper bound',
 referenceDecimalPlaces:100,perturbations:['1e-30','1e-32'],
 checkpointFirstNormalizationMinimum:r.embeddingDenominatorMinimum(),results},null,2));
