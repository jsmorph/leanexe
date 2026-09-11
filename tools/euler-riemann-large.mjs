#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {Readable} from 'node:stream';
import {pipeline} from 'node:stream/promises';
import {createGzip,createGunzip} from 'node:zlib';
import {fileURLToPath} from 'node:url';
import {artifacts,artifactPaths,value,readEventLines,readEvents,verifyEventFile,verifyEventStream} from './euler-2d-runtime.mjs';
import {run2DHostRecord} from './euler-2d-wasmtime-host.mjs';
import {riemannPrimitives} from './euler-2d-oracle.mjs';

const root=fileURLToPath(new URL('../',import.meta.url));
const json=x=>JSON.stringify(x,null,2)+'\n';
const sourceNames=['euler-riemann-large.mjs','euler-riemann-plot.py','riemann-plot-requirements.txt','euler-2d-runtime.mjs','euler-2d-oracle.mjs','euler-2d-wasmtime-host.c','euler-2d-wasmtime-host.mjs'];
const method=n=>({scheme:'First-order finite volume, Rusanov, x then y splitting',gamma:1.4,domain:[0,1,0,1],grid:[n,n],initialInterfaces:[.8,.8],boundary:'Transmissive (clamped neighbors)',targetCfl:.4,acceptedRoundedCflCeiling:.5,endTime:.8,initialization:'Conservative area averages; interface at exact four-fifths of the domain',snapshots:21});
const initialConditions={order:['pressure','density','velocity_x','velocity_y'],quadrants:['bottom-left','bottom-right','top-left','top-right'],states:riemannPrimitives};
const progress=event=>{if(event.kind==='step'&&(event.step%50===0||value(event.t)+value(event.dt)===.8))console.log(`Verified step=${event.step} time=${value(event.t)+value(event.dt)}`);};
async function digest(source){const hash=crypto.createHash('sha256');for await(const chunk of source)hash.update(chunk);return hash.digest('hex');}
const fileHash=file=>digest(fs.createReadStream(file));
function* cellRows(run){
 yield 'i,j,x,y,density,momentum_x,momentum_y,energy,velocity_x,velocity_y,pressure\n';
 const pressure=run.frames.at(-1).densityPressureWords;
 for(let index=0;index<run.n*run.n;index++){
  const q=run.final.gridWords.slice(4*index,4*index+4).map(value),p=value(pressure[2*index+1]);
  const i=index%run.n,j=Math.floor(index/run.n);
  yield [i,j,(i+.5)/run.n,(j+.5)/run.n,...q,q[1]/q[0],q[2]/q[0],p].join(',')+'\n';
 }
}
function* historyRows(run){
 yield 'step,time_before,dt,ratio,alpha,retries,max_cfl,min_density,min_pressure,max_component_velocity,min_energy_density_ratio,boundary_x_mass,boundary_x_momentum_x,boundary_x_momentum_y,boundary_x_energy,boundary_y_mass,boundary_y_momentum_x,boundary_y_momentum_y,boundary_y_energy\n';
 for(const e of run.history)yield [e.step,...[e.t,e.dt,e.ratio,e.alpha].map(value),e.retries,...e.diagnostics.map(value),...e.boundaryX.map(value),...e.boundaryY.map(value)].join(',')+'\n';
}
function result(run){
 const extrema={density:[Infinity,-Infinity],pressure:[Infinity,-Infinity]},words=run.frames.at(-1).densityPressureWords;
 for(let i=0;i<run.n*run.n;i++)for(const [name,v]of [['density',value(words[2*i])],['pressure',value(words[2*i+1])]]){
  extrema[name][0]=Math.min(extrema[name][0],v);extrema[name][1]=Math.max(extrema[name][1],v);
 }
 return {steps:run.steps,retries:run.retries,time:run.t,maxCfl:run.maxCfl,minDensity:run.minDensity,minPressure:run.minPressure,maxComponentVelocity:run.maxVelocityGuard,minEnergyDensityRatio:run.minEnergyRatio,finalExtrema:extrema,calls:run.final.calls,initialTotals:run.final.initialTotals.map(value),finalTotals:run.final.finalTotals.map(value),boundaryIntegral:run.final.boundaryIntegral.map(value),balanceResidual:run.balanceResidual};
}
async function writeParts(record,directory){
 const parts=[],lines=readEventLines(fs.createReadStream(record)),limit=64*1024*1024;
 let pending=await lines.next();
 try{
  while(!pending.done){
   const name=`raw/part-${String(parts.length).padStart(3,'0')}.ndjson.gz`;let bytes=0;
   async function* part(){
    while(!pending.done){
     const line=pending.value+'\n',size=Buffer.byteLength(line);assert.ok(size<=limit,'event exceeds part limit');
     if(bytes&&bytes+size>limit)return;
     bytes+=size;yield line;pending=await lines.next();
    }
   }
   await pipeline(Readable.from(part(),{objectMode:false}),createGzip({level:9}),fs.createWriteStream(path.join(directory,name),{flags:'wx'}));
   parts.push(name);
  }
 }finally{await lines.return();}
 return parts;
}
async function* compressedParts(directory,parts){for(const part of parts)yield* fs.createReadStream(path.join(directory,part));}
function checkRun(run,n){assert.equal(run.scenario,'riemann');assert.equal(run.n,n);assert.equal(run.t,.8);assert.equal(run.frameCount,21);}
export async function writeDataset(record,directory,timing={}){
 assert.ok(!fs.existsSync(directory),'preserve existing dataset');
 const started=performance.now(),run=await verifyEventFile(record,{onEvent:progress});checkRun(run,run.n);
 timing={...timing,replaySeconds:(performance.now()-started)/1000};
 fs.mkdirSync(directory);fs.mkdirSync(path.join(directory,'raw'));
 const parts=await writeParts(record,directory);
 await pipeline(Readable.from(cellRows(run),{objectMode:false}),createGzip({level:9}),fs.createWriteStream(path.join(directory,'cells.csv.gz'),{flags:'wx'}));
 await pipeline(Readable.from(historyRows(run),{objectMode:false}),fs.createWriteStream(path.join(directory,'history.csv'),{flags:'wx'}));
 const sources={},contentSha256={};
 for(const name of sourceNames)sources[name]=await fileHash(path.join(root,'tools',name));
 for(const name of [...parts,'cells.csv.gz','history.csv'])contentSha256[name]=await fileHash(path.join(directory,name));
 const summary={schemaVersion:2,scenario:'riemann',artifacts,sources,node:process.versions.node,runtime:'Wasmtime 44.0.0 C API',
  method:method(run.n),initialConditions,host:{platform:process.platform,arch:process.arch},
  result:result(run),records:{format:'Concatenated gzip members containing newline-delimited JSON events',parts,maxUncompressedPartBytes:64*1024*1024},timing,
  comparison:'Every saved density/pressure word, final conservative word, timestep, control record, diagnostic, and boundary-corrected integral agrees with the independent binary64 JavaScript calculation.',
  proofScope:'The numerical WASM artifacts have exact-byte execution and accepted-state safety theorems. Lean proves axis exchange, clamped sweeps, and successful finite-run call traces. C/JS orchestration, initialization, diagnostics, and plotting use executable tests. PDE convergence remains an open proof obligation.',contentSha256};
 fs.writeFileSync(path.join(directory,'summary.json'),json(summary),{flag:'wx'});
 console.log(json({directory,...summary.result,timing}));return summary;
}
export async function checkDataset(directory){
 const summary=JSON.parse(fs.readFileSync(path.join(directory,'summary.json')));
 assert.equal(summary.schemaVersion,2);assert.deepEqual(summary.artifacts,artifacts);
 assert.equal(summary.scenario,'riemann');assert.equal(summary.node,'24.13.0');assert.equal(summary.runtime,'Wasmtime 44.0.0 C API');
 assert.deepEqual(summary.initialConditions,initialConditions);
 assert.equal(summary.records.format,'Concatenated gzip members containing newline-delimited JSON events');
 assert.equal(summary.records.maxUncompressedPartBytes,64*1024*1024);
 const parts=summary.records.parts;assert.ok(Array.isArray(parts)&&parts.length>0);
 assert.deepEqual(parts,parts.map((_,i)=>`raw/part-${String(i).padStart(3,'0')}.ndjson.gz`));
 assert.deepEqual(Object.keys(summary.contentSha256),[...parts,'cells.csv.gz','history.csv']);
 for(const [name,expected]of Object.entries(summary.contentSha256))assert.equal(await fileHash(path.join(directory,name)),expected,'content hash: '+name);
 const run=await pipeline(Readable.from(compressedParts(directory,parts),{objectMode:false}),createGunzip(),source=>verifyEventStream(readEvents(source),{onEvent:progress}));
 checkRun(run,summary.method.grid[0]);assert.deepEqual(summary.method,method(run.n));
 assert.deepEqual(result(run),summary.result);
 const cellsHash=await pipeline(Readable.from(cellRows(run),{objectMode:false}),createGzip({level:9}),source=>digest(source));
 assert.equal(cellsHash,summary.contentSha256['cells.csv.gz'],'replayed cells CSV');
 assert.equal(await digest(historyRows(run)),summary.contentSha256['history.csv'],'replayed history CSV');
 console.log(json({command:'check',directory,steps:run.steps,time:run.t}));return summary;
}
if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url)){
 assert.equal(process.versions.node,'24.13.0','Node 24.13.0 is required');
 const [command,input,output,...extra]=process.argv.slice(2);assert.equal(extra.length,0);
 if(command==='check'){assert.ok(input&&!output,'usage: check directory');await checkDataset(path.resolve(input));}
 else if(command==='write'){assert.ok(input&&output,'usage: write run.ndjson directory');await writeDataset(path.resolve(input),path.resolve(output));}
 else{
  assert.equal(command,'run','usage: run mesh directory | write run.ndjson directory | check directory');
  const n=Number(input);assert.ok(Number.isInteger(n)&&n>=4&&n<=800&&n%2===0&&output,'usage: run mesh directory');
  assert.ok(!fs.existsSync(output),'preserve existing dataset');
  const started=performance.now();console.log(`Starting native ${n} x ${n} run`);
  const native=run2DHostRecord(...artifactPaths(),n,21,'riemann',{timeout:8*60*60*1000});
  const timing={nativeIncludingBuildSeconds:(performance.now()-started)/1000};
  console.log('Retained native evidence: '+native.evidenceDirectory);
  await writeDataset(native.record,path.resolve(output),timing);
 }
}
