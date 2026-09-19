#!/usr/bin/env node
"use strict";
// Three real QKV calls exercise non-contiguous views, writes and reset.
// Expected arithmetic words come from the original Lean fixture generator.
const fs=require("node:fs"),path=require("node:path"),{spawnSync}=require("node:child_process");
const root=path.resolve(__dirname,"../../..");
const [runtime,shaders,out]=process.argv.slice(2).map(x=>path.resolve(x));
if(!runtime||!shaders||!out)throw Error("usage: packed-host-test.js RUNTIME CHECKED_SHADERS FRESH_OUTPUT");
if(fs.existsSync(out))throw Error("choose a fresh output directory");
fs.mkdirSync(out,{recursive:true});
const read=name=>JSON.parse(fs.readFileSync(path.join(shaders,"vectors",name+".json"),"utf8"));
const qkv=read("qkv"),small=read("small"),vocab=read("vocabularyLeft");
const inner=768,cols=2304,offset=7,bias=offset+inner*cols+11;
const weights=Buffer.alloc(4*(bias+cols));
for(let i=0;i<inner*cols;i++)weights.writeUInt32LE(qkv.b.word,4*(offset+i));
for(let i=0;i<cols;i++)weights.writeUInt32LE(qkv.b.word,4*(bias+i));
const input=Buffer.alloc(4*inner);qkv.a.forEach((word,i)=>input.writeUInt32LE(word,4*i));
fs.writeFileSync(path.join(out,"weights.bin"),weights);fs.writeFileSync(path.join(out,"input.bin"),input);
const wat=fs.readFileSync(path.join(runtime,"model.wat"),"utf8").replace(/\)\s*$/,`  (export "testLinear" (func 23))\n)\n`);
fs.writeFileSync(path.join(out,"test.wat"),wat);
const parsed=spawnSync(process.env.WASM_TOOLS||"wasm-tools",["parse",path.join(out,"test.wat"),"-o",path.join(out,"test.wasm")],{stdio:"inherit"});
if(parsed.error||parsed.status!==0)throw Error("test export assembly failed");
const load=`bytes-file 0 ${out}/weights.bin\nbytes-file 1 ${out}/input.bin\n`;
const call=["arg-ptr 0","arg-ptr 0",`arg-u64 ${weights.length}`,"arg-ptr 1","arg-ptr 1",`arg-u64 ${input.length}`,
  `arg-u64 ${offset}`,`arg-u64 ${bias}`,`arg-u64 ${inner}`,`arg-u64 ${cols}`,"arg-u64 1","call testLinear 3",
  `read-memory result:1 ${cols*4}`,"arg-u64 result:0","call release 0"].join("\n")+"\n";
const script=load+call+`write-bytes 0 ${4*bias} 00000000\n`+call+"call reset 0\n"+load+
  `write-bytes 0 ${4*bias} 000080bf\n`+call+"done\n";
fs.writeFileSync(path.join(out,"commands.txt"),script);
const p=spawnSync(path.join(__dirname,"packed-cpu.sh"),["session",path.join(out,"test.wasm")],
  {cwd:root,env:{...process.env,LEANEXE_PACKED_SHADERS:shaders},input:script,encoding:"utf8",maxBuffer:1024*1024,timeout:60000});
fs.writeFileSync(path.join(out,"execution.log"),(p.stdout||"")+(p.stderr||""));
if(p.error||p.status!==0)throw Error(`host tests failed: ${out}/execution.log`);
const memories=p.stdout.split("\n").filter(s=>s.startsWith("memory ")).map(s=>Buffer.from(s.split(" ")[3],"hex"));
if(memories.length!==3)throw Error("missing memory results");
const first=[qkv.expected.word,vocab.expected.word,small.expected[1]];
memories.forEach((actual,test)=>{
  if(actual.length!==cols*4)throw Error("wrong result size");
  for(let col=0;col<cols;col++)if(actual.readUInt32LE(col*4)!==(col===0?first[test]:qkv.expected.word))
    throw Error(`case ${test} column ${col} differs from Lean fixture`);
});
fs.writeFileSync(path.join(out,"results.json"),JSON.stringify({status:"pass",calls:3,words:3*cols,
  cases:["non-contiguous matrix/bias view","host weight write invalidates GPU copy","reset and reallocation invalidate GPU copy"],
  expectedSource:"original Lean PackedVectors definitions",fullHybridSessionProved:false},null,2)+"\n");
console.log("Three native QKV calls passed: 6,912 exact words, including writes and reset.");
