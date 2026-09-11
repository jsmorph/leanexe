#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {gzipSync} from 'node:zlib';
import {fileURLToPath} from 'node:url';
import {run2D,verifyEvents,artifacts,value} from './euler-2d-runtime.mjs';
import {renderFigures} from './euler-2d-figure.mjs';
const root=fileURLToPath(new URL('../',import.meta.url));
const directory=path.join(root,'data/euler-2d-v1');
const scenarios=['four-quadrants','circular-blast'];
const hash=bytes=>crypto.createHash('sha256').update(bytes).digest('hex');
const json=x=>JSON.stringify(x,null,2)+'\n';
const csv=rows=>rows.map(row=>row.join(',')).join('\n')+'\n';
const command=process.argv[2],records=process.argv.slice(3);
assert.ok(command==='write'||command==='check','usage: node tools/euler-2d-data.mjs write|check [quadrant.ndjson pulse.ndjson]');
assert.ok(records.length===0||(command==='write'&&records.length===2),'retained records are only allowed for an initial write');
assert.equal(process.versions.node,'24.13.0','source tools/macos-env.sh');
if(command==='write')assert.ok(!fs.existsSync(directory),'preserve existing dataset; use check or a new version');
const runs=[],rawRuns=[],files=new Map();
for(const [index,scenario] of scenarios.entries()){
 let run,events;
 if(records.length){
  events=fs.readFileSync(records[index],'utf8').trim().split('\n').map(JSON.parse);
  if(events[0].scenario===undefined)events[0]={kind:'header',scenario,...events[0]};
  run=verifyEvents(events);
 }else{
  run=run2D(192,21,scenario);
  events=fs.readFileSync(path.join(root,run.evidenceDirectory,'run.ndjson'),'utf8').trim().split('\n').map(JSON.parse);
  console.log('Retained native evidence: '+run.evidenceDirectory);
 }
 assert.equal(run.scenario,scenario);assert.equal(run.n,192);assert.equal(run.frames.length,21);
 runs.push(run);rawRuns.push(events);
 const figure=renderFigures(run),prefix=index===0?'quadrants':'pulse';
 files.set(prefix+'.svg',figure.svg);files.set(prefix+'.html',figure.html);
 console.log(JSON.stringify({scenario,n:run.n,steps:run.steps,retries:run.retries,maxCfl:run.maxCfl,balanceResidual:run.balanceResidual}));
}
const sources={};
for(const name of ['euler-2d-data.mjs','euler-2d-runtime.mjs','euler-2d-oracle.mjs','euler-2d-figure.mjs','euler-2d-wasmtime-host.c','euler-2d-wasmtime-host.mjs'])sources[name]=hash(fs.readFileSync(path.join(root,'tools',name)));
const scope='All three numerical WASM modules have exact-byte execution and accepted-safety theorems. Lean proves axis exchange, clamped directional sweeps and successful finite-run call traces. Native C/JS grid/time orchestration, independent numerical comparison, diagnostics and rendering are outside the formal proof. No PDE convergence or exact entropy-solution claim.';
files.set('raw.json.gz',gzipSync(JSON.stringify({schemaVersion:1,artifacts,runs:rawRuns})+'\n',{level:9}));
files.set('summary.json',json({schemaVersion:1,artifacts,sources,node:process.versions.node,runtime:'Wasmtime 44.0.0 C API',
 method:{scheme:'First-order finite volume, Rusanov, x then y splitting',domain:[0,1,0,1],boundary:'Transmissive (clamped neighbors)',gamma:1.4,targetCfl:.4,acceptedRoundedCflCeiling:.5,grid:[192,192],snapshots:21,frameSchedule:'Initial frame, then first accepted state at or beyond each of 20 uniform target times'},
 comparison:'Every raw saved density/pressure word, every final conservative word, every timestep/controller/diagnostic record and boundary-corrected integral match an independent binary64 JavaScript oracle exactly.',
 display:{densityPressure:'Full-run frame extrema rounded outward to two decimals; fixed across all frames',schlieren:'exp(-1.5 * hypot(centered density differences / (2*dx), centered density differences / (2*dy))); clamped boundary differences',orientation:'Physical y increases upward',interpolation:'Cell averages, no smoothing'},
 initialConditions:{'four-quadrants':'Zero velocity, rho=p: lower-left .25, upper-left .4, lower-right .7, upper-right 1. E=2.5*rho.', 'circular-blast':'rho=1, zero velocity; E=5 inside radius1/8 about (.5,.5), E=2.5 outside. Integer cell-center geometry; pressure2 inside,1 outside.'},
 runs:runs.map(({frames,history,final,evidenceDirectory,...r})=>({...r,savedFrames:frames.length,finalStateWords:final.gridWords.length,calls:final.calls,initialTotals:final.initialTotals.map(value),finalTotals:final.finalTotals.map(value),boundaryIntegral:final.boundaryIntegral.map(value)})),
 canonicalContentSha256:Object.fromEntries([...files].map(([name,content])=>[name,hash(content)])),scope}));
const cells=[['scenario','i','j','x','y','density','momentum_x','momentum_y','energy','velocity_x','velocity_y','pressure']];
const history=[['scenario','step','time_before','dt','ratio','alpha','retries','max_cfl','min_density','min_pressure','max_component_velocity','min_energy_density_ratio','boundary_x_mass','boundary_x_momentum_x','boundary_x_momentum_y','boundary_x_energy','boundary_y_mass','boundary_y_momentum_x','boundary_y_momentum_y','boundary_y_energy']];
for(const run of runs){
 for(let index=0;index<run.n*run.n;index++){
  const q=run.final.gridWords.slice(4*index,4*index+4).map(value),i=index%run.n,j=Math.floor(index/run.n);
  cells.push([run.scenario,i,j,(i+.5)/run.n,(j+.5)/run.n,...q,q[1]/q[0],q[2]/q[0],value(run.frames.at(-1).densityPressureWords[2*index+1])]);
 }
 for(const event of run.history)history.push([run.scenario,event.step,...[event.t,event.dt,event.ratio,event.alpha].map(value),event.retries,...event.diagnostics.map(value),...event.boundaryX.map(value),...event.boundaryY.map(value)]);
}
files.set('cells.csv',csv(cells));files.set('history.csv',csv(history));
if(command==='write'){
 fs.mkdirSync(directory);for(const [name,content] of files)fs.writeFileSync(path.join(directory,name),content,{flag:'wx'});
}else for(const [name,content] of files)assert.ok(fs.readFileSync(path.join(directory,name)).equals(Buffer.from(content)),'dataset mismatch: '+name);
console.log(command+' passed: '+files.size+' reproducible files, '+[...files.values()].reduce((n,v)=>n+Buffer.byteLength(v),0)+' bytes');
