import fs from 'node:fs';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {run as hostRun, flux as hostFlux} from './euler-sod-oracle.mjs';
import {fileURLToPath} from 'node:url';
const root=fileURLToPath(new URL('../',import.meta.url));
export const artifacts=Object.freeze({scan:'279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9',step:'bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297'});
const wordBuffer=Buffer.alloc(8);
const bits=x=>{wordBuffer.writeDoubleLE(x);return wordBuffer.readBigUInt64LE();};
const value=x=>{wordBuffer.writeBigUInt64LE(BigInt.asUintN(64,x));return wordBuffer.readDoubleLE();};
const word=x=>BigInt.asUintN(64,x).toString(16).padStart(16,'0');
async function load(name,sha){
  const bytes=fs.readFileSync(root+'/proofs/artifacts/'+name+'/'+sha+'/program.wasm');
  assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),sha);
  const {module,instance}=await WebAssembly.instantiate(bytes,{});
  assert.deepEqual(WebAssembly.Module.imports(module),[]);
  return instance.exports;
}
export async function runFrozen(n=100, {capture=false}={}) {
assert.ok(Number.isSafeInteger(n)&&n>=2&&n<=1000&&n%2===0);
const scan=await load('euler_grid_scan',artifacts.scan);
const step=await load('euler_grid_step',artifacts.step);
const dx=1/n,end=.2,count=1+6*n,objectBytes=64+48*n,arenaEnd=4096+(n+6)*objectBytes;
const inputPointer=arenaEnd+48,required=inputPointer+8+24*n;
if(step.memory.buffer.byteLength<required)step.memory.grow(Math.ceil(required/65536)-step.memory.buffer.byteLength/65536);
assert.ok(step.memory.buffer.byteLength/65536<=65536);
const put=(memory,p,data)=>{const d=new DataView(memory.buffer);assert.ok(p+8+8*data.length<=d.byteLength);d.setBigUint64(p,BigInt(data.length),true);data.forEach((x,i)=>d.setBigUint64(p+8+8*i,x,true));};
let grid=Array.from({length:n},(_,i)=>i<n/2?[1,0,2.5]:[.125,0,.25]).flat().map(bits);
let t=0,steps=0,maxCfl=0,minRho=Infinity,minPressure=Infinity;const history=[],frames=[],initial=[0,0,0],boundaryIntegral=[0,0,0];
for(let i=0;i<n;i++)for(let k=0;k<3;k++)initial[k]+=value(grid[3*i+k])*dx;
while(t<end){
  assert.ok(steps<10000);put(scan.memory,64,grid);
  const [status,speed]=scan.maxSpeedCheckedBits(64n);assert.equal(status,0n);
  const alpha=value(speed);assert.ok(Number.isFinite(alpha)&&alpha>0);
  const dt=Math.min(.45*dx/alpha,end-t),ratio=dt/dx;assert.ok(dt>0&&t+dt>t&&t+dt<=end);
  step.reset();assert.equal(step.allocCount.value,0n);assert.equal(step.releaseCount.value,0n);assert.equal(step.freeCount.value,0n);
  put(step.memory,inputPointer,grid);
  const pointer=Number(step.stepCheckedBits(bits(ratio),BigInt(inputPointer))),d=new DataView(step.memory.buffer);
  assert.ok(Number.isSafeInteger(pointer)&&4096+48<=pointer&&pointer+8+8*count<=arenaEnd);
  assert.equal(d.getBigUint64(pointer,true),BigInt(count));assert.equal(d.getBigUint64(pointer+8,true),0n);
  const next=[],outputWords=[];let stepCfl=0,stepRho=Infinity,stepPressure=Infinity;
  for(let i=0;i<n;i++){
    const fields=Array.from({length:6},(_,k)=>d.getBigUint64(pointer+8+8*(1+6*i+k),true));
    const numeric=fields.map(value);assert.ok(numeric.every(Number.isFinite));assert.ok(numeric[0]>0&&numeric[3]>0&&numeric[4]>0&&numeric[5]>0&&numeric[5]<=.5);
    outputWords.push(...fields.map(word));stepCfl=Math.max(stepCfl,numeric[5]);stepRho=Math.min(stepRho,numeric[0]);stepPressure=Math.min(stepPressure,numeric[3]);
    next.push(...fields.slice(0,3));maxCfl=Math.max(maxCfl,numeric[5]);minRho=Math.min(minRho,numeric[0]);minPressure=Math.min(minPressure,numeric[3]);
  }
  assert.equal(step.allocCount.value,BigInt(1+6*n));assert.equal(step.releaseCount.value,BigInt(5*n+1));assert.equal(step.freeCount.value,BigInt(5*n+1));
  const left=grid.slice(0,3).map(value),right=grid.slice(-3).map(value);
  const fl=hostFlux(left,left).value,fr=hostFlux(right,right).value;
  for(let k=0;k<3;k++)boundaryIntegral[k]+=dt*(fr[k]-fl[k]);
  steps++;history.push({step:steps,t:word(bits(t)),dt:word(bits(dt)),ratio:word(bits(ratio)),alpha:word(speed),time:t+dt,maxCfl:stepCfl,minDensity:stepRho,minPressure:stepPressure,boundaryFluxLeft:fl,boundaryFluxRight:fr});
  if(capture)frames.push({step:steps,time:t+dt,outputWords:[word(0n),...outputWords]});
  grid=next;t+=dt;
}
const oracle=hostRun(n);assert.equal(steps,oracle.steps);assert.equal(t,oracle.t);assert.deepEqual(grid,oracle.cells.flat().map(bits));
const summary={evidence:'Exact-byte-verified WASM exports; generic Lean recurrence/call-trace theorem. Host controller, preparation, measurements and oracle are regression evidence.',n,steps,t,maxCfl,minRho,minPressure,exactHostWordMatch:true,inputPointer,arenaEnd,memoryBytes:step.memory.buffer.byteLength,allocationsPerStep:1+6*n,releasesPerStep:5*n+1};
const total=[0,0,0];for(let i=0;i<n;i++)for(let k=0;k<3;k++)total[k]+=value(grid[3*i+k])*dx;
const balanceResidual=total.map((x,k)=>x-initial[k]+boundaryIntegral[k]);
assert.deepEqual(balanceResidual,oracle.balanceResidual);
return {...summary,initialIntegrals:initial,finalIntegrals:total,boundaryIntegral,balanceResidual,history,gridWords:grid.map(word),...(capture?{frames}:{})};
}
export const decodeWord=s=>value(BigInt('0x'+s));
