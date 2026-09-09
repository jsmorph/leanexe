import fs from 'node:fs';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {run as hostRun,flux as hostFlux} from './euler-sod-oracle.mjs';
import {runSodHost} from './euler-wasmtime-host.mjs';
const root=fileURLToPath(new URL('../',import.meta.url));
export const artifacts=Object.freeze({scan:'279a3bca462b4acdeeef840ab0c7c9649070c7595f47de3b7748a986d02f14c9',step:'bc546b72e740ec6e953dc3c01e88a44c19fd914c109c64a33e8d8edcabfe2297'});
const wordBuffer=Buffer.alloc(8);
const bits=x=>{wordBuffer.writeDoubleLE(x);return wordBuffer.readBigUInt64LE().toString(16).padStart(16,'0');};
export const decodeWord=s=>{assert.match(s,/^[0-9a-f]{16}$/);wordBuffer.writeBigUInt64LE(BigInt('0x'+s));return wordBuffer.readDoubleLE();};
function artifact(name,sha){const file=root+'/proofs/artifacts/'+name+'/'+sha+'/program.wasm';assert.equal(crypto.createHash('sha256').update(fs.readFileSync(file)).digest('hex'),sha);return file;}
export async function runFrozen(n=100,{capture=false}={}){
 assert.ok(Number.isSafeInteger(n)&&n>=2&&n<=1000&&n%2===0);
 const records=runSodHost(artifact('euler_grid_scan',artifacts.scan),artifact('euler_grid_step',artifacts.step),n,capture);
 const layout=records.shift().layout,final=records.pop();assert.equal(layout.n,n);
 const dx=1/n,arenaEnd=4096+(n+6)*(64+48*n);assert.equal(layout.arenaEnd,arenaEnd);assert.equal(layout.inputPointer,arenaEnd+48);assert.ok(layout.memoryBytes>=arenaEnd+56+24*n&&layout.memoryBytes/65536<=65536);
 let t=0,maxCfl=0,minRho=Infinity,minPressure=Infinity;const history=[],frames=[],initial=[0,0,0],boundaryIntegral=[0,0,0];
 for(let i=0;i<n;i++){const q=i<n/2?[1,0,2.5]:[.125,0,.25];for(let k=0;k<3;k++)initial[k]+=q[k]*dx;}
 for(const row of records){
  assert.equal(row.step,history.length+1);assert.equal(row.t,bits(t));const dt=decodeWord(row.dt),alpha=decodeWord(row.alpha),ratio=decodeWord(row.ratio);
  assert.ok(Number.isFinite(alpha)&&alpha>0);assert.equal(dt,Math.min(.45*dx/alpha,.2-t));assert.equal(ratio,dt/dx);assert.ok(dt>0&&t+dt>t&&t+dt<=.2);
  const cfl=decodeWord(row.maxCfl),rho=decodeWord(row.minDensity),pressure=decodeWord(row.minPressure);assert.ok(Number.isFinite(cfl)&&cfl>0&&cfl<=.5&&Number.isFinite(rho)&&rho>0&&Number.isFinite(pressure)&&pressure>0);
  maxCfl=Math.max(maxCfl,cfl);minRho=Math.min(minRho,rho);minPressure=Math.min(minPressure,pressure);
  assert.equal(row.boundaryWords.length,6);const left=row.boundaryWords.slice(0,3).map(decodeWord),right=row.boundaryWords.slice(3).map(decodeWord),fl=hostFlux(left,left).value,fr=hostFlux(right,right).value;
  for(let k=0;k<3;k++)boundaryIntegral[k]+=dt*(fr[k]-fl[k]);
  history.push({step:row.step,t:row.t,dt:row.dt,ratio:row.ratio,alpha:row.alpha,time:t+dt,maxCfl:cfl,minDensity:rho,minPressure:pressure,boundaryFluxLeft:fl,boundaryFluxRight:fr});
  if(capture){assert.equal(row.outputWords.length,1+6*n);assert.equal(row.outputWords[0],bits(0));for(let i=0;i<n;i++){const q=row.outputWords.slice(1+6*i,1+6*i+6).map(decodeWord);assert.ok(q.every(Number.isFinite)&&q[0]>0&&q[3]>0&&q[4]>0&&q[5]>0&&q[5]<=.5);}frames.push({step:row.step,time:t+dt,outputWords:row.outputWords});}
  t+=dt;
 }
 assert.equal(final.finalTime,bits(.2));assert.equal(t,.2);assert.equal(final.gridWords.length,3*n);
 const oracle=hostRun(n);assert.equal(records.length,oracle.steps);assert.deepEqual(final.gridWords,oracle.cells.flat().map(bits));
 const total=[0,0,0];for(let i=0;i<n;i++)for(let k=0;k<3;k++)total[k]+=decodeWord(final.gridWords[3*i+k])*dx;
 const balanceResidual=total.map((x,k)=>x-initial[k]+boundaryIntegral[k]);assert.deepEqual(balanceResidual,oracle.balanceResidual);
 return {evidence:'Exact-byte-verified WASM through Wasmtime44. Generic Lean recurrence/call-trace theorem; C/JS host controller, preparation, measurements and oracle remain outside the proof.',n,steps:records.length,t,maxCfl,minRho,minPressure,exactHostWordMatch:true,inputPointer:layout.inputPointer,arenaEnd,memoryBytes:layout.memoryBytes,allocationsPerStep:1+6*n,releasesPerStep:5*n+1,initialIntegrals:initial,finalIntegrals:total,boundaryIntegral,balanceResidual,history,gridWords:final.gridWords,...(capture?{frames}:{})};
}
