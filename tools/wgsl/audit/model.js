"use strict";
// Diagnostic transcription of the fixed binary64 evaluation order. It is
// checked against Lean's integer floating-point model and the existing Wasm;
// it is not a replacement for either proof.
const scratch = Buffer.alloc(8);
const fromWord = w => { scratch.writeBigUInt64LE(BigInt(w)); return scratch.readDoubleLE(); };
const word = x => { scratch.writeDoubleLE(x); return scratch.readBigUInt64LE().toString(); };
const c = h => fromWord(BigInt(`0x${h}`));
const expCoefficients = ["3CA6827863B97D97","3CE952C77030AD4A","3D2AE7F3E733B81F","3D6AE7F3E733B81F",
  "3DA93974A8C07C9D","3DE6124613A86D09","3E21EED8EFF8D898","3E5AE64567F544E4","3E927E4FB7789F5C",
  "3EC71DE3A556C734","3EFA01A01A01A01A","3F2A01A01A01A01A","3F56C16C16C16C17","3F81111111111111",
  "3FA5555555555555","3FC5555555555555","3FE0000000000000","3FF0000000000000","3FF0000000000000"].map(c);
function expNeg(x) {
  if (x < -64) return 0;
  let squares = 0;
  while (x < -1 && squares < 6) { x *= 0.5; squares++; }
  let p = expCoefficients[0];
  for (let i=1;i<expCoefficients.length;i++) p = p*x+expCoefficients[i];
  while (squares-- > 0) p *= p;
  return p;
}
function gelu(x) {
  const negative = x < 0 || Object.is(x, -0), a = Math.abs(x);
  if (a > 8) return negative ? 0 : x;
  const square = a*a, factor = square*c("3FA6E4E26D4801F7")+1;
  const z = -(factor*a*c("3FF9884533D43651")), e=expNeg(z), d=1+e;
  return negative ? (-a*e)/d : a/d;
}
const sum4 = x => (x[0]+x[1])+(x[2]+x[3]);
const sum8 = x => sum4(x.slice(0,4))+sum4(x.slice(4));
const add = (a,b) => a.map((x,i)=>x+b[i]);
function model(bytes) {
  const w=Array.from({length:2488},(_,i)=>bytes.readDoubleLE(8*i));
  function norm(x,offset) {
    const mean=sum4(x)/4, z=x.map(a=>a-mean), sigma=Math.sqrt(sum4(z.map(a=>a*a))/4+c("3EE4F8B588E368F1"));
    return z.map((a,i)=>(a/sigma)*w[offset+i]+w[offset+4+i]);
  }
  function matrix(x,offset,n) { return Array.from({length:n},(_,j)=>
    (x.length===4?sum4:sum8)(x.map((a,i)=>a*w[offset+i*n+j]))); }
  function probabilities(s) { const m=Math.max(...s), e=s.map(x=>expNeg(x-m)), d=sum4(e); return e.map(x=>x/d); }
  function forward(tokens) {
    const embedding=tokens.map((t,p)=>Array.from({length:4},(_,i)=>w[t*4+i]+w[1024+p*4+i]));
    const norm1=embedding.map(x=>norm(x,2464));
    const query=matrix(norm1[3],1040,4), keys=norm1.map(x=>matrix(x,1056,4)), values=norm1.map(x=>matrix(x,1072,4));
    const scores=[0,1].map(h=>keys.map(k=>(query[2*h]*k[2*h]+query[2*h+1]*k[2*h+1])/c("3FF6A09E667F3BCD")));
    const probability=scores.map(probabilities);
    const attended=Array.from({length:4},(_,j)=>sum4(values.map((v,k)=>probability[j>>1][k]*v[j])));
    const attentionProjection=matrix(attended,1088,4), attention=add(attentionProjection,w.slice(1104,1108));
    const residual1=add(embedding[3],attention), norm2=norm(residual1,2472);
    const expanded=add(matrix(norm2,1108,8),w.slice(1140,1148)), activated=expanded.map(gelu);
    const contractProjection=matrix(activated,1148,4), contracted=add(contractProjection,w.slice(1180,1184));
    const residual2=add(residual1,contracted), hidden=norm(residual2,2480);
    const head64=add(matrix(hidden,1184,256),w.slice(2208,2464));
    const mixed=Array.from({length:256},(_,j)=>{
      let acc=0;
      for(let i=0;i<4;i++)acc=Math.fround(acc+Math.fround(Math.fround(hidden[i])*Math.fround(w[1184+i*256+j])));
      return acc+w[2208+j];
    });
    return {embedding,norm1,query,keys,values,scores,probability,attended,attentionProjection,attention,residual1,norm2,
      expanded,activated,contractProjection,contracted,residual2,hidden,head64,mixed};
  }
  return {w,norm,matrix,probabilities,forward};
}
module.exports = { model, word, fromWord, expNeg, gelu, sum4, sum8, add };
