#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import crypto from 'node:crypto';
import assert from 'node:assert/strict';
import {fileURLToPath} from 'node:url';
import {runFrozen,decodeWord,artifacts} from './euler-sod-runtime.mjs';
import {average,referenceSummary} from './euler-sod-riemann.mjs';
import {side} from './euler-sod-oracle.mjs';
const root=fileURLToPath(new URL('../',import.meta.url));
const directory=path.join(root,'data/euler-sod-v2');
const json=x=>JSON.stringify(x,null,2)+'\n';
const csv=rows=>rows.map(row=>row.join(',')).join('\n')+'\n';
const derived=q=>[...q,q[1]/q[0],side(q).p];
function figure(cells,refs,rows){
 const w=1320,h=930,parts=[
  '<svg xmlns="http://www.w3.org/2000/svg" width="1320" height="930" viewBox="0 0 1320 930" role="img" aria-labelledby="title desc">',
  '<title id="title">Sod shock tube from verified WebAssembly</title>',
  '<desc id="desc">Five state profiles at time0.2 and grid refinement against exact Riemann conservative cell averages. Rendering and scientific comparison are host calculations.</desc>',
  '<rect width="1320" height="930" fill="#101a2b"/><g font-family="Arial, sans-serif" fill="#e9f0f7">',
  '<text x="54" y="56" font-size="29" font-weight="700">A shock tube, step by checked step</text>',
  '<text x="54" y="88" font-size="16" fill="#aebbd0">Stationary Sod · 100 cells · t = 0.2 · 93 accepted Rusanov steps · gamma = 1.4</text>',
  '<path d="M840 57h26" stroke="#53d9d1" stroke-width="3"/><text x="877" y="62" font-size="14">Verified WASM</text>',
  '<path d="M1050 57h26" stroke="#f4b86a" stroke-width="2" stroke-dasharray="5 4"/><text x="1087" y="62" font-size="14">Exact reference</text>'
 ];
 const labels=['Density','Momentum','Total energy','Velocity','Pressure'];
 const a=cells.map(derived),b=refs.map(derived);
 for(let k=0;k<6;k++){
  const x=54+(k%3)*425,y=143+Math.floor(k/3)*344,pw=340,ph=225;
  parts.push('<text x="'+x+'" y="'+(y-13)+'" font-size="18" font-weight="700">'+(labels[k]||'Refinement · conservative L1 error')+'</text>');
  const max=k<5?Math.max(...a.map(q=>q[k]),...b.map(q=>q[k]))*1.08:1;
  const px=i=>x+pw*i,py=v=>y+ph-ph*v/max;
  for(let j=0;j<=4;j++){
   const yy=y+ph*j/4;
   parts.push('<path d="M'+x+' '+yy+'h'+pw+'" stroke="#2b3b51"/>');
   parts.push('<text x="'+(x-8)+'" y="'+(yy+4)+'" text-anchor="end" font-size="11" fill="#9fb0c8">'+(k<5?(max*(1-j/4)).toFixed(2):['0.1','0.032','0.01','0.0032','0.001'][j])+'</text>');
  }
  if(k<5){
   for(const [data,color,dash] of [[b,'#f4b86a','5 4'],[a,'#53d9d1','']]){
    const points=data.map((q,i)=>px((i+.5)/data.length).toFixed(2)+','+py(q[k]).toFixed(2)).join(' ');
    parts.push('<polyline points="'+points+'" fill="none" stroke="'+color+'" stroke-width="2.4" stroke-dasharray="'+dash+'"/>');
   }
   for(const t of [0,.25,.5,.75,1])parts.push('<text x="'+px(t)+'" y="'+(y+ph+22)+'" text-anchor="middle" font-size="12" fill="#9fb0c8">'+t+'</text>');
   parts.push('<text x="'+(x+pw/2)+'" y="'+(y+ph+46)+'" text-anchor="middle" font-size="12" fill="#9fb0c8">Position x</text>');
  }else{
   for(const [field,color] of [[0,'#53d9d1'],[1,'#f4b86a'],[2,'#beadff']]){
    const points=rows.map((r,i)=>px(i/3)+','+(y+ph*(-1-Math.log10(r.l1[field]))/2));
    parts.push('<polyline points="'+points.join(' ')+'" fill="none" stroke="'+color+'" stroke-width="2.5"/>');
   }
   rows.forEach((r,i)=>parts.push('<text x="'+px(i/3)+'" y="'+(y+ph+22)+'" text-anchor="middle" font-size="12" fill="#9fb0c8">'+r.n+'</text>'));
   parts.push('<text x="'+x+'" y="'+(y+ph+46)+'" font-size="12" fill="#53d9d1">Density</text><text x="'+(x+95)+'" y="'+(y+ph+46)+'" font-size="12" fill="#f4b86a">Momentum</text><text x="'+(x+220)+'" y="'+(y+ph+46)+'" font-size="12" fill="#beadff">Energy</text>');
  }
 }
 parts.push('<path d="M54 808h1212" stroke="#2b3b51"/>',
  '<text x="54" y="842" font-size="16">Max CFL 0.4500</text><text x="350" y="842" font-size="16">Minimum density 0.125</text><text x="720" y="842" font-size="16">Minimum pressure 0.100</text>',
  '<text x="54" y="876" font-size="13" fill="#aebbd0">Exact-byte execution + accepted-state safety are proved. Riemann comparison and refinement are numerical validation.</text>',
  '<text x="54" y="900" font-size="12" fill="#8095b0">First-order finite volume · transmissive boundaries · no reconstruction · data/euler-sod-v2</text></g></svg>');
 return parts.join('\n')+'\n';
}
async function build(){
 assert.equal(process.versions.node,'24.13.0','use the pinned tools/macos-env.sh environment');
 const rows=[],runs=[];
 for(const n of [100,200,400,800]){
  const data=await runFrozen(n,{capture:n===100}),l1=[0,0,0];
  for(let i=0;i<n;i++){const ref=average(i/n,(i+1)/n);for(let k=0;k<3;k++)l1[k]+=Math.abs(decodeWord(data.gridWords[3*i+k])-ref[k])/n;}
  if(rows.length)assert.ok(l1.every((x,k)=>x<rows.at(-1).l1[k]));
  const {history,gridWords,frames,...summary}=data;rows.push({...summary,l1});runs.push(data);
  console.log(JSON.stringify({n,steps:data.steps,maxCfl:data.maxCfl,l1}));
 }
 const first=runs[0],cells=Array.from({length:100},(_,i)=>first.gridWords.slice(3*i,3*i+3).map(decodeWord));
 const refs=Array.from({length:100},(_,i)=>average(i/100,(i+1)/100));
 const sources={};for(const name of ['euler-sod-data.mjs','euler-sod-runtime.mjs','euler-sod-oracle.mjs','euler-sod-riemann.mjs','euler-wasmtime-host.c','euler-wasmtime-host.mjs'])sources[name]=crypto.createHash('sha256').update(fs.readFileSync(path.join(root,'tools',name))).digest('hex');
 const summary={schemaVersion:1,artifacts,sources,node:process.versions.node,runtime:'Wasmtime 44.0.0 C API',referenceSummary,rows,scope:'WASM step/scan/reset are exact-byte verified. Generic Lean recurrence and call-trace theorem is conditional on accepted outputs and host-prepared memory. C/JS host controller, diagnostics, oracle and rendering are outside the proof. No convergence theorem.'};
 const fileCells=[['cell','x','density','momentum','energy','velocity','pressure','alpha','courant','reference_density','reference_momentum','reference_energy']];
 cells.forEach((q,i)=>{const fields=first.frames.at(-1).outputWords.slice(1+6*i,1+6*i+6).map(decodeWord);fileCells.push([i,(i+.5)/100,...q,q[1]/q[0],...fields.slice(3),...refs[i]]);});
 return new Map([
  ['raw.json',json({schemaVersion:1,artifacts,runs})],['summary.json',json(summary)],
  ['cells.csv',csv(fileCells)],['history.csv',csv([['step','time','dt','max_speed','courant','min_density','min_pressure','boundary_mass_left','boundary_momentum_left','boundary_energy_left','boundary_mass_right','boundary_momentum_right','boundary_energy_right'],...first.history.map(r=>[r.step,r.time,decodeWord(r.dt),decodeWord(r.alpha),r.maxCfl,r.minDensity,r.minPressure,...r.boundaryFluxLeft,...r.boundaryFluxRight])])],
  ['refinement.csv',csv([['cells','steps','L1_density','L1_momentum','L1_energy','balance_density','balance_momentum','balance_energy'],...rows.map(r=>[r.n,r.steps,...r.l1,...r.balanceResidual])])],
  ['cell-averages.svg',figure(cells,refs,rows)]
 ]);
}
const command=process.argv[2];assert.ok(command==='write'||command==='check','usage: node tools/euler-sod-data.mjs write|check');
const files=await build();
if(command==='write'){
 for(const name of files.keys())assert.ok(!fs.existsSync(path.join(directory,name)),'refusing to overwrite '+name);
 fs.mkdirSync(directory,{recursive:true});for(const [name,content]of files)fs.writeFileSync(path.join(directory,name),content,{flag:'wx'});
}else for(const [name,content]of files)assert.equal(fs.readFileSync(path.join(directory,name),'utf8'),content,'dataset mismatch: '+name);
console.log(command+' passed: '+files.size+' reproducible dataset files');
