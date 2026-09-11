#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {execFileSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {initial} from './euler-2d-oracle.mjs';
import {artifactPaths,word} from './euler-2d-runtime.mjs';

const root=fileURLToPath(new URL('../',import.meta.url));
const sha=x=>crypto.createHash('sha256').update(x).digest('hex');
const json=x=>JSON.stringify(x,null,2)+'\n';
const blockName=(i,suffix)=>`block-${String(i).padStart(2,'0')}.${suffix}`;
const rows=(n,i)=>Math.floor(n*(i+1)/24)-Math.floor(n*i/24);
const blockFile=(dir,i,suffix)=>path.join(dir,blockName(i,suffix));
export function build(){
 const api=process.env.WASMTIME_C_API;assert.ok(api&&path.basename(api).startsWith('wasmtime-v44.0.0-'));
 const sources=['euler-block-host.c','euler-block-worker.wat'],flags=['-std=c11','-O2','-Wall','-Wextra','-Werror','-fno-fast-math','-ffp-contract=off'];
 const artifacts=artifactPaths(),input={sources:Object.fromEntries(sources.map(n=>[n,sha(fs.readFileSync(path.join(root,'tools',n)))])),artifacts:artifacts.map(p=>sha(fs.readFileSync(p))),flags,api,platform:process.platform,arch:process.arch};
 const directory=path.join(root,'build/tools/euler-block-'+sha(json(input))),host=path.join(directory,'worker'),receipt=path.join(directory,'receipt.json');
 if(fs.existsSync(directory)){
  assert.ok(fs.existsSync(receipt),'preserve incomplete build');const saved=JSON.parse(fs.readFileSync(receipt));assert.deepEqual(saved.input,input);
  for(const [name,hash]of Object.entries(saved.files))assert.equal(sha(fs.readFileSync(path.join(directory,name))),hash);
 }else{
  fs.mkdirSync(directory);
  execFileSync('cc',[...flags,'-I'+path.join(api,'include'),path.join(root,'tools',sources[0]),'-L'+path.join(api,'lib'),'-lwasmtime','-Wl,-rpath,'+path.join(api,'lib'),'-o',host],{timeout:120000,stdio:'inherit'});
  execFileSync(host,['prepare',directory,...artifacts,path.join(root,'tools',sources[1])],{timeout:120000,stdio:'inherit'});
  const files=Object.fromEntries(fs.readdirSync(directory).map(n=>[n,sha(fs.readFileSync(path.join(directory,n)))]));
  fs.writeFileSync(receipt,json({input,files}),{flag:'wx'});
 }
 return {directory,host,receipt};
}
function totals(directory,n){
 const sum=[0,0,0,0],correction=[0,0,0,0],area=(1/n)*(1/n);
 for(let b=0;b<24;b++){
  const data=fs.readFileSync(blockFile(directory,b,'bin'));assert.equal(data.length,rows(n,b)*n*40);
  for(let p=0;p<data.length;p+=40)for(let k=0;k<4;k++){
   const term=data.readDoubleLE(p+8*k)*area-correction[k],next=sum[k]+term;correction[k]=(next-sum[k])-term;sum[k]=next;
  }
 }
 return sum;
}
function initialize(directory,n){
 const cells=initial(n,'riemann');
 for(let b=0;b<24;b++){
  const start=Math.floor(n*b/24)*n,count=rows(n,b)*n,data=Buffer.alloc(count*40);
  for(let i=0;i<count;i++){
   const q=cells[start+i];for(let k=0;k<4;k++)data.writeDoubleLE(q[k],40*i+8*k);
  }
  fs.writeFileSync(blockFile(directory,b,'bin'),data,{flag:'wx'});
 }
}
function fields(directory,n,pressure){
 const words=[];
 for(let b=0;b<24;b++){
  const data=fs.readFileSync(blockFile(directory,b,'bin'));assert.equal(data.length,rows(n,b)*n*40);
  for(let p=0;p<data.length;p+=40){
   if(pressure)words.push(data.readBigUInt64LE(p).toString(16).padStart(16,'0'),data.readBigUInt64LE(p+32).toString(16).padStart(16,'0'));
   else for(let k=0;k<4;k++)words.push(data.readBigUInt64LE(p+8*k).toString(16).padStart(16,'0'));
  }
 }
 return words;
}
function metadata(directory){return Array.from({length:24},(_,i)=>{const b=fs.readFileSync(blockFile(directory,i,'meta'));assert.equal(b.length,64);return {status:Number(b.readBigUInt64LE()),calls:Number(b.readBigUInt64LE(8)),alpha:b.readDoubleLE(16),metrics:Array.from({length:5},(_,k)=>b.readDoubleLE(24+8*k))};});}
function boundary(x,y,n){
 const bx=[0,0,0,0],by=[0,0,0,0];
 for(let b=0;b<24;b++){
  const data=fs.readFileSync(blockFile(x,b,'boundary'));assert.equal(data.length,rows(n,b)*32);
  for(let p=0;p<data.length;p+=32)for(let k=0;k<4;k++)bx[k]+=data.readDoubleLE(p+8*k);
 }
 const low=fs.readFileSync(blockFile(y,0,'boundary')),high=fs.readFileSync(blockFile(y,23,'boundary'));assert.equal(low.length,n*32);assert.equal(high.length,n*32);
 for(let i=0;i<n;i++)for(let k=0;k<4;k++)by[k]+=high.readDoubleLE(i*32+8*k)-low.readDoubleLE(i*32+8*k);
 return [bx,by];
}
export function runBlocks(n,directory,{maxSteps=10000}={}){
 assert.ok(Number.isInteger(n)&&n>=24&&n<=800&&n%2===0);assert.ok(!fs.existsSync(directory),'preserve existing run');
 const compiled=build(),started=performance.now();fs.mkdirSync(directory);const raw=path.join(directory,'initial-input'),first=path.join(directory,'initial');fs.mkdirSync(raw);fs.mkdirSync(first);initialize(raw,n);
 execFileSync('bash',[path.join(root,'tools/euler-block-wave.sh'),compiled.host,compiled.directory,'init',String(n),raw,first,word(0)],{timeout:120000,stdio:'inherit'});
 const initialized=metadata(first);assert.ok(initialized.every((m,i)=>m.status===0&&m.calls===rows(n,i)*n));
 const record=path.join(directory,'run.ndjson'),fd=fs.openSync(record,'wx'),recordHash=crypto.createHash('sha256');
 const emit=x=>{const line=JSON.stringify(x)+'\n';fs.writeSync(fd,line);recordHash.update(line);};
 let current=first,t=0,steps=0,retries=0,nextFrame=1,cellCalls=0;const initialTotals=totals(first,n),balance=[0,0,0,0],physicalCalls=[n*n,0,0];
 const frame=()=>emit({kind:'frame',index:nextFrame++,step:steps,t:word(t),densityPressureWords:fields(current,n,true)});
 emit({kind:'header',scenario:'riemann',n,frames:21,endTime:word(.8),targetCfl:word(.4)});nextFrame=0;frame();
 const wave=(mode,input,output,ratio)=>{
  fs.mkdirSync(output);execFileSync('bash',[path.join(root,'tools/euler-block-wave.sh'),compiled.host,compiled.directory,mode,String(n),input,output,word(ratio)],{timeout:120000,stdio:'inherit'});
  const meta=metadata(output);
  if(mode==='scan')physicalCalls[0]+=meta.reduce((s,m)=>s+m.calls,0);
  else{physicalCalls[2]+=meta.reduce((s,m)=>s+m.calls,0);physicalCalls[1]+=meta.reduce((s,m,i)=>s+(m.status?0:mode==='x'?2*rows(n,i):(i===0||i===23?n:0)),0);}
  return meta;
 };
 try{
  while(t<.8&&steps<maxSteps){
   const stepdir=path.join(directory,`step-${String(steps+1).padStart(5,'0')}`);fs.mkdirSync(stepdir);
   const scan=wave('scan',current,path.join(stepdir,'scan'),0);assert.ok(scan.every(m=>m.status===0));const alpha=Math.max(...scan.map(m=>m.alpha));assert.ok(Number.isFinite(alpha)&&alpha>0);
   let dt=Math.min(.4*(1/n)/alpha,.8-t),attempts=0,mx,my,x,y,ratio;
   const account=meta=>{const first=meta.findIndex(m=>m.status!==0),end=first<0?meta.length:first+1;cellCalls+=meta.slice(0,end).reduce((s,m)=>s+m.calls,0);return first<0;};
   for(;;){
    assert.ok(attempts<24&&dt>0&&t+dt>t&&t+dt<=.8);ratio=dt/(1/n);
    const attempt=path.join(stepdir,`try-${String(attempts).padStart(2,'0')}`);fs.mkdirSync(attempt);x=path.join(attempt,'x');y=path.join(attempt,'y');
    mx=wave('x',current,x,ratio);
    if(account(mx)){my=wave('y',x,y,ratio);if(account(my))break;}
    attempts++;retries++;dt*=.5;
   }
   const metrics=[0,Infinity,Infinity,0,Infinity];for(const m of [...mx,...my])for(let k=0;k<5;k++){assert.ok(Number.isFinite(m.metrics[k]));metrics[k]=(k===0||k===3?Math.max:Math.min)(metrics[k],m.metrics[k]);}
   const [bx,by]=boundary(x,y,n);for(let k=0;k<4;k++)balance[k]+=dt*(1/n)*(bx[k]+by[k]);
   emit({kind:'step',step:++steps,t:word(t),dt:word(dt),ratio:word(ratio),alpha:word(alpha),retries:attempts,diagnostics:metrics.map(word),boundaryX:bx.map(word),boundaryY:by.map(word)});
   current=y;t+=dt;while(nextFrame<21&&t>=.8*nextFrame/20)frame();
   if(steps%10===0||t===.8)console.log(`step=${steps} time=${t} retries=${retries}`);
  }
  assert.equal(t,.8,'step limit reached; partial evidence preserved');const finalTotals=totals(current,n),residual=finalTotals.map((v,k)=>v-initialTotals[k]+balance[k]);
  emit({kind:'final',steps,retries,t:word(t),calls:[n*n*(2*steps+1),4*n*steps,cellCalls],initialTotals:initialTotals.map(word),finalTotals:finalTotals.map(word),boundaryIntegral:balance.map(word),balanceResidual:residual.map(word),gridWords:fields(current,n,false)});
 }finally{fs.closeSync(fd);}
 const sources=Object.fromEntries(['euler-block-host.c','euler-block-worker.wat','euler-block-run.mjs','euler-block-wave.sh','euler-2d-oracle.mjs','euler-2d-runtime.mjs'].map(name=>[name,sha(fs.readFileSync(path.join(root,'tools',name)))]));
 const execution={workers:24,n,steps,retries,seconds:(performance.now()-started)/1000,node:process.versions.node,sources,recordSha256:recordHash.digest('hex'),buildReceipt:JSON.parse(fs.readFileSync(compiled.receipt)),physicalCalls,recordCalls:'Calls in serial cell order; speculative calls on rejected attempts are counted in physicalCalls.',finalBlocks:path.relative(directory,current)};
 fs.writeFileSync(path.join(directory,'execution.json'),json(execution),{flag:'wx'});console.log(json(execution));return record;
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url)){
 assert.equal(process.versions.node,'24.13.0');const [command,n,output]=process.argv.slice(2);
 if(command==='build')console.log(json(build()));else{assert.equal(command,'run');runBlocks(Number(n),path.resolve(output));}
}
