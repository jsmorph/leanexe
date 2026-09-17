"use strict";
// Unverified diagnostic prototypes. Does not emit or modify any Wasm/WGSL.
const assert=require('node:assert/strict');
const {cases,adversarial}=require('./cases'),{model,sum4,add,gelu,word}=require('./model'),{arithmetic}=require('./real');
function alternative(bytes,tokens,stableAttention){
  const m=model(bytes),{w}=m;
  const center=x=>{const mean=sum4(x)/4;return x.map(v=>v-mean);};
  const normParts=(parts,offset)=>{
    const centered=parts.map(center),x=Array.from({length:4},(_,i)=>centered.reduce((s,p)=>s+p[i],0));
    return m.norm(x,offset);
  };
  const parts=tokens.map((t,p)=>[w.slice(t*4,t*4+4),w.slice(1024+p*4,1028+p*4)]);
  const n1=parts.map(p=>normParts(p,2464)),q=m.matrix(n1[3],1040,4),k=n1.map(x=>m.matrix(x,1056,4)),v=n1.map(x=>m.matrix(x,1072,4));
  const scores=[0,1].map(h=>k.map(x=>(q[2*h]*x[2*h]+q[2*h+1]*x[2*h+1])/Math.SQRT2));
  const p=scores.map(m.probabilities);
  const attended=Array.from({length:4},(_,j)=>{
    const s=scores[j>>1],max=Math.max(...s),min=Math.min(...s);
    if(!stableAttention||max-min>0.5)return sum4(v.map((x,i)=>p[j>>1][i]*x[j]));
    const mean=sum4(v.map(x=>x[j]))/4,d=s.map(x=>Math.expm1(x-max));
    return mean+sum4(v.map((x,i)=>d[i]*(x[j]-mean)))/(4+sum4(d));
  });
  const r1parts=[...parts[3],m.matrix(attended,1088,4),w.slice(1104,1108)];
  const n2=normParts(r1parts,2472),expanded=add(m.matrix(n2,1108,8),w.slice(1140,1148)),activated=expanded.map(gelu);
  const r2parts=[...r1parts,m.matrix(activated,1148,4),w.slice(1180,1184)],hidden=normParts(r2parts,2480);
  const head64=add(m.matrix(hidden,1184,256),w.slice(2208,2464));
  const mixed=Array.from({length:256},(_,j)=>{
    let acc=0;for(let i=0;i<4;i++)acc=Math.fround(acc+Math.fround(Math.fround(hidden[i])*Math.fround(w[1184+256*i+j])));
    return acc+w[2208+j];
  });
  return {hidden,head64,mixed};
}
const inputs=cases();
// Fixed wider family; both signs and larger/smaller exactly representable deltas.
for(const exponent of [-60,-50,-40])for(const sign of [-1,1]){
  const weights=adversarial(sign);for(let i=0;i<4;i++)weights.writeDoubleLE(sign*2**exponent*(i<2?1:-1),8*(1036+i));
  inputs.push({name:`adversarial-${sign>0?'plus':'minus'}-2^${exponent}`,tokens:[0,1,2,3],weights});
}
const results=inputs.map(input=>{
  const real=arithmetic(120,input.weights),ideal=real.forward(input.tokens);
  const variants=[['current',model(input.weights).forward(input.tokens)],
    ['center-components',alternative(input.weights,input.tokens,false)],
    ['center-components-and-expm1-attention',alternative(input.weights,input.tokens,true)]];
  const compared=variants.map(([name,x])=>({name,evenLogit:x.head64[0],
    hiddenError:real.maxError(x.hidden.map(v=>real.fromWord(word(v))),ideal.hidden),
    head64Error:real.maxError(x.head64.map(v=>real.fromWord(word(v))),ideal.logits),
    mixedError:real.maxError(x.mixed.map(v=>real.fromWord(word(v))),ideal.logits)}));
  assert(compared.every(x=>Number.isFinite(x.mixedError)));
  // Regressions of these twelve fixed diagnostics, not a domain-wide certificate.
  assert(compared[2].head64Error<1e-13,input.name+' prototype binary64 accuracy');
  assert(compared[2].mixedError<2e-6,input.name+' prototype mixed accuracy');
  return {name:input.name,idealEvenLogit:real.number(ideal.logits[0]),variants:compared};
});
console.log(JSON.stringify({schemaVersion:1,status:'pass',scope:'unverified binary64 prototypes, including native Math.expm1; finite cases, no uniform guarantee',
 referenceDecimalPlaces:120,nearUniformAttentionSpreadLimit:0.5,results},null,2));
