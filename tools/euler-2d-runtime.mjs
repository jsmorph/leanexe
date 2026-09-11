import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {StringDecoder} from 'node:string_decoder';
import {side,flux,cell,swap,initial,scenarios,endTime,NumericalRejection} from './euler-2d-oracle.mjs';
import {run2DHost} from './euler-2d-wasmtime-host.mjs';
const root=fileURLToPath(new URL('../',import.meta.url));
const buffer=Buffer.alloc(8);
export const word=x=>{buffer.writeDoubleLE(x);return buffer.readBigUInt64LE().toString(16).padStart(16,'0');};
export const value=s=>{assert.match(s,/^[0-9a-f]{16}$/);buffer.writeBigUInt64LE(BigInt('0x'+s));return buffer.readDoubleLE();};
export const artifacts=[
 {case:'euler2_d_conservative',sha256:'607008ccfe4c7cc7c721aa459eb7c5442cbeb569b7281b9958f2cdce87132a1d',bytes:3193,export:'sideCheckedBits',index:13},
 {case:'euler2_d_dynamic_flux',sha256:'a35295b198aba7800be2f36c10c73d928225b11ac8a1fce8eb00f6848aef2995',bytes:4495,export:'fluxCheckedBits',index:25},
 {case:'euler2_d_cell_step',sha256:'5bf42c31171b77f5480a15f48e26117b7956b5718fcfe3fb6f0d2dd5b75ed942',bytes:6171,export:'cellCheckedBits',index:35},
];
function total(cells,n){
 const sum=[0,0,0,0],correction=[0,0,0,0],area=(1/n)*(1/n);
 for(const q of cells)for(let k=0;k<4;k++){const term=q[k]*area-correction[k],next=sum[k]+term;correction[k]=(next-sum[k])-term;sum[k]=next;}
 return sum;
}
function boundary(cells,n,y){
 const result=[0,0,0,0];
 for(let i=0;i<n;i++){
  let a=cells[y?i:i*n],b=cells[y?(n-1)*n+i:i*n+n-1];if(y){a=swap(a);b=swap(b);}
  let low=flux(a,a).value,high=flux(b,b).value;if(y){low=swap(low);high=swap(high);}
  for(let k=0;k<4;k++)result[k]+=high[k]-low[k];
 }
 return result;
}
function sweep(cells,n,y,ratio,metrics,calls){
 const next=[],pressure=[];
 for(let j=0;j<n;j++)for(let i=0;i<n;i++){
  const index=j*n+i,previous=y?Math.max(0,j-1)*n+i:j*n+Math.max(0,i-1),following=y?Math.min(n-1,j+1)*n+i:j*n+Math.min(n-1,i+1);
  let l=cells[previous],q=cells[index],r=cells[following];if(y){l=swap(l);q=swap(q);r=swap(r);}
  calls.count++;const out=cell(ratio,l,q,r),v=out.state;
  next[index]=y?swap(v):v;pressure[index]=out.p;
  metrics[0]=Math.max(metrics[0],out.courant);metrics[1]=Math.min(metrics[1],v[0]);metrics[2]=Math.min(metrics[2],out.p);
  metrics[3]=Math.max(metrics[3],Math.max(Math.abs(v[1]),Math.abs(v[2]))/v[0]);metrics[4]=Math.min(metrics[4],v[3]/v[0]);
 }
 return {cells:next,pressure};
}
function* eventVerifier({retainFrames=true}={}){
 const header=yield;assert.equal(header.kind,'header');
 const scenario=header.scenario??'four-quadrants';assert.ok(scenarios.includes(scenario));const end=endTime(scenario);
 const n=header.n,frames=header.frames;assert.ok(Number.isInteger(n)&&n>=4&&n<=800&&n%2===0);assert.ok(Number.isInteger(frames)&&frames>=2&&frames<=65);
 assert.equal(header.endTime,word(end));assert.equal(header.targetCfl,word(.4));
 let cells=initial(n,scenario),pressure=cells.map(q=>side(q).p),t=0,steps=0,frameIndex=0,retries=0;
 const initialTotals=total(cells,n),balance=[0,0,0,0],calls={count:0},history=[],savedFrames=[];
 for(;;){
  const event=yield;
  if(event.kind==='frame'){
   assert.equal(event.index,frameIndex++);assert.equal(event.step,steps);assert.equal(event.t,word(t));
   assert.deepEqual(event.densityPressureWords,cells.flatMap((q,i)=>[word(q[0]),word(pressure[i])]),'raw frame '+event.index);
   if(retainFrames)savedFrames.push(event);else savedFrames[0]=event;
   continue;
  }
  if(event.kind==='step'){
   assert.ok(t<end&&steps<10000);let alpha=0;for(const q of cells)alpha=Math.max(alpha,side(q).speed,side(swap(q)).speed);
   let dt=Math.min(.4*(1/n)/alpha,end-t),attempts=0,middle,next,metrics,ratio;
   for(;;){
    assert.ok(attempts<24);assert.ok(dt>0&&t+dt>t&&t+dt<=end);ratio=dt/(1/n);metrics=[0,Infinity,Infinity,0,Infinity];
    try{middle=sweep(cells,n,false,ratio,metrics,calls);next=sweep(middle.cells,n,true,ratio,metrics,calls);break;}
    catch(error){if(!(error instanceof NumericalRejection))throw error;attempts++;dt*=.5;}
   }
   const bx=boundary(cells,n,false),by=boundary(middle.cells,n,true);for(let k=0;k<4;k++)balance[k]+=dt*(1/n)*(bx[k]+by[k]);
   const expected={kind:'step',step:++steps,t:word(t),dt:word(dt),ratio:word(ratio),alpha:word(alpha),retries:attempts,diagnostics:metrics.map(word),boundaryX:bx.map(word),boundaryY:by.map(word)};
   assert.deepEqual(event,expected,'complete step '+steps);history.push(event);retries+=attempts;cells=next.cells;pressure=next.pressure;t+=dt;continue;
  }
  assert.equal(event.kind,'final');assert.equal(t,end);assert.equal(frameIndex,frames);
  assert.equal(savedFrames.at(-1).t,word(t),'final frame time');
  const finalTotals=total(cells,n),residual=finalTotals.map((v,k)=>v-initialTotals[k]+balance[k]);
  assert.deepEqual(event,{kind:'final',steps,retries,t:word(t),calls:[n*n*(2*steps+1),4*n*steps,calls.count],initialTotals:initialTotals.map(word),finalTotals:finalTotals.map(word),boundaryIntegral:balance.map(word),balanceResidual:residual.map(word),gridWords:cells.flatMap(q=>q.map(word))},'complete raw final result');
  return {scenario,n,steps,retries,t,history,frames:savedFrames,frameCount:frameIndex,final:event,
   maxCfl:Math.max(...history.map(x=>value(x.diagnostics[0]))),
   minDensity:Math.min(...history.map(x=>value(x.diagnostics[1]))),
   minPressure:Math.min(...history.map(x=>value(x.diagnostics[2]))),
   maxVelocityGuard:Math.max(...history.map(x=>value(x.diagnostics[3]))),
   minEnergyRatio:Math.min(...history.map(x=>value(x.diagnostics[4]))),balanceResidual:residual};
 }
}
export function verifyEvents(events){
 assert.ok(Array.isArray(events)&&events.length>=4);
 const verifier=eventVerifier();let result=verifier.next();
 for(const event of events){assert.ok(!result.done,'event after final result');result=verifier.next(event);}
 assert.ok(result.done,'missing final event');return result.value;
}
export async function* readEventLines(source){
 let fragments=[],bytes=0;const decoder=new StringDecoder('utf8');
 function append(fragment){bytes+=Buffer.byteLength(fragment);assert.ok(bytes<=64*1024*1024,'event exceeds 64 MiB');fragments.push(fragment);}
 for await(const data of source){
  const chunk=decoder.write(typeof data==='string'?Buffer.from(data):data);let start=0;
  for(let end=chunk.indexOf('\n');end!==-1;end=chunk.indexOf('\n',start)){
   append(chunk.slice(start,end));const line=fragments.join('');fragments=[];bytes=0;
   assert.ok(line.length>0,'empty event record');yield line;start=end+1;
  }
  if(start<chunk.length)append(chunk.slice(start));
 }
 const tail=decoder.end();if(tail)append(tail);
 if(fragments.length)yield fragments.join('');
}
export async function* readEvents(source){
 for await(const line of readEventLines(source))yield JSON.parse(line);
}
export async function verifyEventStream(events,{retainFrames=false,onEvent=()=>{}}={}){
 const verifier=eventVerifier({retainFrames});let result=verifier.next();
 for await(const event of events){
  assert.ok(!result.done,'event after final result');result=verifier.next(event);await onEvent(event);
 }
 assert.ok(result.done,'missing final event');return result.value;
}
export function verifyEventFile(file,options){
 return verifyEventStream(readEvents(fs.createReadStream(file,{encoding:'utf8'})),options);
}
export function artifactPaths(){
 return artifacts.map(a=>{const p=path.join(root,'proofs/artifacts',a.case,a.sha256,'program.wasm'),bytes=fs.readFileSync(p);assert.equal(bytes.length,a.bytes);assert.equal(crypto.createHash('sha256').update(bytes).digest('hex'),a.sha256);return p;});
}
export function run2D(n=192,frames=21,scenario='four-quadrants'){
 const paths=artifactPaths();
 const native=run2DHost(...paths,n,frames,scenario);const verified=verifyEvents(native.events);
 return {...verified,evidenceDirectory:native.evidenceDirectory};
}
