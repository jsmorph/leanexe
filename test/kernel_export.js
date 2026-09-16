#!/usr/bin/env node
const crypto=require("node:crypto");
const path=require("node:path");
const {assert,fs,host,run,compile,leanArray,reference,dir}=require("./kernel_helpers");
const {decodeExport}=require("../tools/kernel-export-format");
const {checkExportFile}=require("../tools/kernel-check-export");
const fixtures="test/fixtures/kernel-check";
const raw=fs.readFileSync(`${fixtures}/identity.ndjson`,"utf8");
const bad=fs.readFileSync(`${fixtures}/identity-corrupt.ndjson`,"utf8");
const decoded=decodeExport(raw), corrupt=decodeExport(bad);
assert.deepEqual(decoded,JSON.parse(fs.readFileSync(`${fixtures}/identity.decoded.json`,"utf8")),"exact decoded structure");
const expectedBad=structuredClone(decoded);expectedBad.graph[17]="2";
assert.deepEqual(corrupt,expectedBad,"corruption changes only the inner lambda body");
const manifest=JSON.parse(fs.readFileSync(`${fixtures}/provenance.json`,"utf8"));
for(const [file,digest] of Object.entries(manifest.sha256)){
  assert.equal(crypto.createHash("sha256").update(fs.readFileSync(file)).digest("hex"),digest,file);
}
const mutations=[
  ["wrong Lean",r=>{r[0].meta.lean.githash="wrong";}],
  ["wrong format",r=>{r[0].meta.format.version="3.0.0";}],
  ["name gap",r=>{r[1].in=99;}],
  ["name forward reference",r=>{r[1].str.pre=99;}],
  ["expression gap",r=>{r.find(x=>x.ie===0).ie=99;}],
  ["forward child",r=>{r.find(x=>x.ie===5).lam.body=99;}],
  ["huge index",r=>{r.find(x=>x.ie===1).bvar=2**53;}],
  ["constant dependency",r=>{const i=r.findIndex(x=>x.ie===0);r[i]={ie:0,const:{name:1,us:[]}};}],
  ["axiom dependency",r=>{r.splice(1,0,{axiom:{name:1,type:0}});}],
  ["symbolic universe",r=>{r.splice(1,0,{il:1,param:1});}],
  ["universe parameters",r=>{r.at(-1).thm.levelParams=[2];}],
  ["missing proof body",r=>{delete r.at(-1).thm.value;}],
  ["extra declaration",r=>{r.push(structuredClone(r.at(-1)));}],
  ["wrong theorem block",r=>{r.at(-1).thm.all=[1,2];}],
];
for(const [name,mutate] of mutations){
  const records=raw.trim().split("\n").map(JSON.parse);mutate(records);
  assert.throws(()=>decodeExport(records.map(r=>JSON.stringify(r)).join("\n")),undefined,name);
}
const artifact=compile("Export","checkExport","m0-11");
const native=reference("Export",[decoded,corrupt].flatMap(c=>[
  `(checkScope ${leanArray(c.graph)} ${c.term} 0 1000).toNat`,
  `(checkExport ${leanArray(c.graph)} ${c.term} ${c.claimed} 10000).toNat`,
]));
assert.deepEqual(native,["0","0","0","1"],"both inputs are scoped; only the real proof typechecks");
for(const [c,expected] of [[decoded,0n],[corrupt,1n]]){
  assert.equal(host.callI64(artifact,"checkExport",[host.arrayU64(c.graph),host.i64(c.term),host.i64(c.claimed),host.i64(10000)]),expected);
}
assert.equal(checkExportFile(artifact,`${fixtures}/identity.ndjson`).status,0);
assert.equal(checkExportFile(artifact,`${fixtures}/identity-corrupt.ndjson`).status,1);
assert.equal(checkExportFile(artifact,`${fixtures}/identity.ndjson`,"1").status,5);
const output=JSON.parse(run([process.execPath,"tools/kernel-check-export.js",artifact,`${fixtures}/identity.ndjson`]));
assert.equal(output.result,"accepted");assert.deepEqual(output.axioms,[]);
// Inspect the import section as bytes; execution is exclusively via Wasmtime.
const bytes=fs.readFileSync(artifact);let cursor=8;
assert.equal(bytes.subarray(0,8).toString("hex"),"0061736d01000000");
function leb(){let n=0,scale=1;for(let i=0;i<5;i++){const b=bytes[cursor++];assert.notEqual(b,undefined);n+=(b&127)*scale;if(!(b&128))return n;scale*=128;}throw new Error("invalid section length");}
while(cursor<bytes.length){const section=bytes[cursor++],length=leb(),end=cursor+length;assert(end<=bytes.length);if(section===2)assert.equal(leb(),0,"checker must be import-free");cursor=end;}
const receipt={artifact,bytes:bytes.length,sha256:crypto.createHash("sha256").update(bytes).digest("hex"),declaration:decoded.name,accepted:0,corruptRejected:1,exhausted:5};
fs.writeFileSync(path.join(dir,"m0-11-receipt.json"),JSON.stringify(receipt,null,2)+"\n");
console.log(`checked real export, scoped corruption, exhaustion, ${mutations.length} adapter failures, exact decoded bytes and import-free WASM; artifact: ${artifact}`);
