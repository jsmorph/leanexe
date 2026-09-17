// Independent numerical diagnostic, not a formal real-arithmetic proof.
const assert=require('node:assert/strict');
function arithmetic(digits,bytes){
  const S=10n**BigInt(digits), abs=x=>x<0n?-x:x;
  const mul=(a,b)=>a*b/S, div=(a,b)=>a*S/b;
  function isqrt(x){assert(x>=0n);if(x<2n)return x;let a=1n<<BigInt(Math.ceil(x.toString(2).length/2));for(;;){const b=(a+x/a)/2n;if(b>=a)return a;a=b;}}
  const sqrt=x=>isqrt(x*S);
  function exp(x){if(x<0n)return div(S,exp(-x));let n=0;while(x>S/4n){x/=2n;n++;}let sum=S,term=S;for(let k=1n;;k++){term=mul(term,x)/k;if(term===0n)break;sum+=term;}while(n-->0)sum=mul(sum,sum);return sum;}
  function tanh(x){if(x<0n)return -tanh(-x);const e=exp(2n*x);return div(e-S,e+S);}
  function atanInverse(n){let power=S/n,total=0n;for(let k=0n;;k++){const term=power/(2n*k+1n);if(term===0n)break;total+=(k%2n===0n?term:-term);power/=n*n;}return total;}
  const pi=16n*atanInverse(5n)-4n*atanInverse(239n);
  const geluScale=sqrt(div(2n*S,pi)), geluC=S*44715n/1000000n;
  const gelu=x=>mul(x,S+tanh(mul(geluScale,x+mul(geluC,mul(mul(x,x),x)))))/2n;
  function fromWord(word){word=BigInt(word);const sign=(word>>63n)?-1n:1n,e=Number((word>>52n)&2047n),f=word&((1n<<52n)-1n);assert(e!==2047);const m=e===0?f:f+(1n<<52n);const shift=(e===0?-1022:e-1023)-52;return sign*(shift>=0?(m<<BigInt(shift))*S:m*S/(1n<<BigInt(-shift)));}
  const number=x=>Number(x)/Number(S);
  const w=Array.from({length:2488},(_,i)=>fromWord(bytes.readBigUInt64LE(8*i)));
  const sum=x=>x.reduce((a,b)=>a+b,0n);
  const epsilon=S/100000n;
  function norm(x,off){const mean=sum(x)/4n,z=x.map(y=>y-mean),sigma=sqrt(sum(z.map(y=>mul(y,y)))/4n+epsilon);return {sigma,h:z.map((y,i)=>mul(div(y,sigma),w[off+i])+w[off+4+i])};}
  function matrix(x,off,n){return Array.from({length:n},(_,j)=>sum(x.map((a,i)=>mul(a,w[off+i*n+j]))));}
  const add=(x,y)=>x.map((a,i)=>a+y[i]);
  const probabilities=row=>{const max=row.reduce((a,b)=>a>b?a:b),e=row.map(x=>exp(x-max)),den=sum(e);return e.map(x=>div(x,den));};
  const stageNames=['embedding','norm1','query','keys','values','scores','probability','attended',
    'attentionProjection','attention','residual1','norm2','expanded','activated','contractProjection',
    'contracted','residual2','hidden','head64','mixed'];
  function stage(name,t,tokens){
    switch(name){
      case 'embedding':return tokens.map((token,p)=>Array.from({length:4},(_,i)=>w[token*4+i]+w[1024+p*4+i]));
      case 'norm1':return t.embedding.map(x=>norm(x,2464).h);
      case 'query':return matrix(t.norm1[3],1040,4);
      case 'keys':return t.norm1.map(x=>matrix(x,1056,4));
      case 'values':return t.norm1.map(x=>matrix(x,1072,4));
      case 'scores':return [0,1].map(h=>t.keys.map(k=>div(mul(t.query[2*h],k[2*h])+mul(t.query[2*h+1],k[2*h+1]),sqrt(2n*S))));
      case 'probability':return t.scores.map(probabilities);
      case 'attended':return Array.from({length:4},(_,j)=>sum(t.values.map((v,k)=>mul(t.probability[j>>1][k],v[j]))));
      case 'attentionProjection':return matrix(t.attended,1088,4);
      case 'attention':return add(t.attentionProjection,w.slice(1104,1108));
      case 'residual1':return add(t.embedding[3],t.attention);
      case 'norm2':return norm(t.residual1,2472).h;
      case 'expanded':return add(matrix(t.norm2,1108,8),w.slice(1140,1148));
      case 'activated':return t.expanded.map(gelu);
      case 'contractProjection':return matrix(t.activated,1148,4);
      case 'contracted':return add(t.contractProjection,w.slice(1180,1184));
      case 'residual2':return add(t.residual1,t.contracted);
      case 'hidden':return norm(t.residual2,2480).h;
      case 'head64':case 'mixed':return add(matrix(t.hidden,1184,256),w.slice(2208,2464));
      default:throw Error('unknown stage '+name);
    }
  }
  function forward(tokens,override=(name,x)=>x){
    const trace={};
    for(const name of stageNames)trace[name]=override(name,stage(name,trace,tokens));
    return {trace,hidden:trace.hidden,logits:trace.head64,
      denominators:{norm1:trace.embedding.map(x=>number(norm(x,2464).sigma)),norm2:number(norm(trace.residual1,2472).sigma),normFinal:number(norm(trace.residual2,2480).sigma)},
      maxScore:Math.max(...trace.scores.flat().map(x=>Math.abs(number(x)))),maxHidden:Math.max(...trace.hidden.map(x=>Math.abs(number(x))))};
  }
  function maxError(a,b){return number(a.map((x,i)=>abs(x-b[i])).reduce((a,b)=>a>b?a:b,0n));}
  function embeddingDenominatorMinimum(){let min=null,where=null;for(let t=0;t<256;t++)for(let p=0;p<4;p++){const x=Array.from({length:4},(_,i)=>w[t*4+i]+w[1024+p*4+i]);const sigma=norm(x,2464).sigma;if(min===null||sigma<min){min=sigma;where={token:t,position:p};}}return {value:number(min),where};}
  return {digits,S,number,fromWord,forward,maxError,embeddingDenominatorMinimum,stage,stageNames,exp,gelu,norm};
}
module.exports={arithmetic};
