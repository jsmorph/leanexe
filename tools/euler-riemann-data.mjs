#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {gzipSync,gunzipSync} from 'node:zlib';
import {fileURLToPath} from 'node:url';
import {run2D,verifyEvents,artifacts,value} from './euler-2d-runtime.mjs';
import {riemannPrimitives} from './euler-2d-oracle.mjs';
const root=fileURLToPath(new URL('../',import.meta.url));
const directory=path.join(root,'data/euler-riemann-v1');
const [command,record,...extra]=process.argv.slice(2);
assert.ok(['write','check'].includes(command)&&extra.length===0,'usage: node tools/euler-riemann-data.mjs write|check [run.ndjson]');
assert.equal(process.versions.node,'24.13.0','Node 24.13.0 is required');
if(command==='write')assert.ok(!fs.existsSync(directory),'preserve existing dataset');
const hash=bytes=>crypto.createHash('sha256').update(bytes).digest('hex');
const json=x=>JSON.stringify(x,null,2)+'\n';
const csv=rows=>rows.map(row=>row.join(',')).join('\n')+'\n';
let events,run;
if(record)events=fs.readFileSync(record,'utf8').trim().split('\n').map(JSON.parse);
else if(command==='check'){
 const saved=JSON.parse(gunzipSync(fs.readFileSync(path.join(directory,'raw.json.gz'))));
 assert.equal(saved.schemaVersion,1);assert.deepEqual(saved.artifacts,artifacts);events=saved.events;
}else{
 const native=run2D(192,21,'riemann');run=native;
 console.log('Retained native evidence: '+native.evidenceDirectory);
 events=fs.readFileSync(path.join(root,native.evidenceDirectory,'run.ndjson'),'utf8').trim().split('\n').map(JSON.parse);
}
run??=verifyEvents(events);
assert.equal(run.scenario,'riemann');assert.equal(run.n,192);assert.equal(run.t,.8);assert.equal(run.frames.length,21);
const cells=[['i','j','x','y','density','momentum_x','momentum_y','energy','velocity_x','velocity_y','pressure']];
const pressureWords=run.frames.at(-1).densityPressureWords;
const extrema={density:[Infinity,-Infinity],pressure:[Infinity,-Infinity]};
for(let index=0;index<run.n*run.n;index++){
 const q=run.final.gridWords.slice(4*index,4*index+4).map(value),p=value(pressureWords[2*index+1]);
 const i=index%run.n,j=Math.floor(index/run.n);
 cells.push([i,j,(i+.5)/run.n,(j+.5)/run.n,...q,q[1]/q[0],q[2]/q[0],p]);
 for(const [name,v]of [['density',q[0]],['pressure',p]]){extrema[name][0]=Math.min(extrema[name][0],v);extrema[name][1]=Math.max(extrema[name][1],v);}
}
const history=[['step','time_before','dt','ratio','alpha','retries','max_cfl','min_density','min_pressure','max_component_velocity','min_energy_density_ratio','boundary_x_mass','boundary_x_momentum_x','boundary_x_momentum_y','boundary_x_energy','boundary_y_mass','boundary_y_momentum_x','boundary_y_momentum_y','boundary_y_energy']];
for(const event of run.history)history.push([event.step,...[event.t,event.dt,event.ratio,event.alpha].map(value),event.retries,...event.diagnostics.map(value),...event.boundaryX.map(value),...event.boundaryY.map(value)]);
const files=new Map([
 ['raw.json.gz',gzipSync(JSON.stringify({schemaVersion:1,artifacts,events})+'\n',{level:9})],
 ['cells.csv',csv(cells)],['history.csv',csv(history)],
]);
const sources={};
for(const name of ['euler-riemann-data.mjs','euler-riemann-plot.py','riemann-plot-requirements.txt','euler-2d-runtime.mjs','euler-2d-oracle.mjs','euler-2d-wasmtime-host.c','euler-2d-wasmtime-host.mjs'])sources[name]=hash(fs.readFileSync(path.join(root,'tools',name)));
files.set('summary.json',json({
 schemaVersion:1,scenario:'riemann',artifacts,sources,node:process.versions.node,runtime:'Wasmtime 44.0.0 C API',
 method:{scheme:'First-order finite volume, Rusanov, x then y splitting',gamma:1.4,domain:[0,1,0,1],grid:[192,192],initialInterfaces:[.8,.8],boundary:'Transmissive (clamped neighbors)',targetCfl:.4,acceptedRoundedCflCeiling:.5,endTime:.8,initialization:'Conservative area averages; interface at exact four-fifths of the domain',snapshots:21},
 initialConditions:{order:['pressure','density','velocity_x','velocity_y'],quadrants:['bottom-left','bottom-right','top-left','top-right'],states:riemannPrimitives},
 result:{steps:run.steps,retries:run.retries,time:run.t,maxCfl:run.maxCfl,minDensity:run.minDensity,minPressure:run.minPressure,maxComponentVelocity:run.maxVelocityGuard,minEnergyDensityRatio:run.minEnergyRatio,finalExtrema:extrema,calls:run.final.calls,initialTotals:run.final.initialTotals.map(value),finalTotals:run.final.finalTotals.map(value),boundaryIntegral:run.final.boundaryIntegral.map(value),balanceResidual:run.balanceResidual},
 comparison:'Every saved density/pressure word, final conservative word, timestep, control record, diagnostic, and boundary-corrected integral agrees with the independent binary64 JavaScript calculation.',
 proofScope:'The numerical WASM artifacts have exact-byte execution and accepted-state safety theorems. Lean proves axis exchange, clamped sweeps, and successful finite-run call traces. C/JS orchestration, initialization, diagnostics, and plotting use executable tests. PDE convergence remains an open proof obligation.',
 contentSha256:Object.fromEntries([...files].map(([name,content])=>[name,hash(content)])),
}));
if(command==='write'){
 fs.mkdirSync(directory);for(const [name,content]of files)fs.writeFileSync(path.join(directory,name),content,{flag:'wx'});
}else for(const [name,content]of files)assert.ok(fs.readFileSync(path.join(directory,name)).equals(Buffer.from(content)),'dataset mismatch: '+name);
console.log(JSON.stringify({command,steps:run.steps,retries:run.retries,maxCfl:run.maxCfl,minDensity:run.minDensity,minPressure:run.minPressure,finalExtrema:extrema,balanceResidual:run.balanceResidual}));
