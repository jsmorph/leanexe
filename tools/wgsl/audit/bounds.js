"use strict";
// Recompute the existing proved recurrence, without changing its coefficients.
const B=4,eps=2**-52,L=Math.sqrt(1/100000),p=12*B*B+1;
const stages=[];
function node(name,local,...terms){
  const contributions={[name]:local};
  for(const [gain,prior] of terms)for(const [source,value] of Object.entries(prior.contributions))
    contributions[source]=(contributions[source]||0)+gain*value;
  const total=Object.values(contributions).reduce((a,b)=>a+b,0);
  const result={name,local,total,contributions};stages.push(result);return result;
}
const c4=m=>(12*(m*B+1)+6)*eps,c8=m=>(32*(m*B+1)+22)*eps,norm=m=>(16000*B*m+254*B+2)*eps;
const embedding=node('embedding',(2*B+1)*eps);
const norm1=node('norm1',norm(21),[2*B/L,embedding]);
const projection=node('projection',c4(31),[4*B,norm1]);
const score=node('score',(16*p*p+3)*eps,[2*(p+12*B*B),projection]);
const attended=node('attended',(10077*p+6)*eps,[2*p,score],[1,projection]);
const residual1=node('residual1',(50041+50019)*eps+c4(1250),[1,embedding],[4*B,attended]);
const norm2=node('norm2',norm(60000),[2*B/L,residual1]);
const expanded=node('expanded',1259*eps+c4(31),[4*B,norm2]);
const activated=node('activated',200000*eps,[4,expanded]);
const contracted=node('contracted',100909*eps+c8(1261),[8*B,activated]);
const residual2=node('residual2',160910*eps,[1,residual1],[1,contracted]);
const hidden=node('hidden',norm(200000),[2*B/L,residual2]);
const mixed=node('mixed',1/10000,[16,hidden]);
const sources=Object.entries(mixed.contributions).map(([name,contribution])=>({name,contribution,fraction:contribution/mixed.total})).sort((a,b)=>b.contribution-a.contribution);
const ranges={embedding:2*B,normalizedL1:8*B,normalizedCoordinate:(1+Math.sqrt(3))*B,
 projection:8*B*B,score:64*Math.SQRT2*B**4,attended:8*B*B,residual1:32*B**3+3*B,
 expanded:8*B*B+B,residual2:96*B**3+8*B*B+4*B,logit:8*B*B+B};
console.log(JSON.stringify({schemaVersion:1,status:'pass',scope:'existing formal-bound recurrence evaluated numerically; improved real ranges are mathematical derivations in the report',
 B,arithmeticEpsilon:eps,normalizationFloor:L,stages,sources,derivedRealRanges:ranges,
 derivedNormalizationLipschitz:1.5*B/L,existingNormalizationLipschitz:2*B/L,
 parentMainMagnitudeCap:1260+12*B*B+B},null,2));
