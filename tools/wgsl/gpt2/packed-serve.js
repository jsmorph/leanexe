#!/usr/bin/env node
"use strict";
const fs=require("node:fs"),path=require("node:path"),http=require("node:http");
const bundle=path.resolve(process.argv[2]||"build/gpt2/packed-bundle"),port=Number(process.argv[3]||8080);
const publicRoot=path.join(__dirname,"packed-browser");
const files=new Set(["model.wasm","model-cpu.wasm","sampler.wasm","tokenizer.wasm","transfer.wasm","tokenizer.bin","weights.bin","manifest.json",
  ...["qkv","attention","expansion","projection","vocabularyLeft","vocabularyRight"].map(r=>`shaders/${r}/kernel.wgsl`)]);
const publicFiles=new Set(["index.html","app.js","host.js","worker.js"]);
const types={".html":"text/html; charset=utf-8",".js":"text/javascript; charset=utf-8",".wasm":"application/wasm",".json":"application/json",".wgsl":"text/plain"};
const server=http.createServer((req,res)=>{
  res.setHeader("Cross-Origin-Opener-Policy","same-origin");res.setHeader("Cross-Origin-Embedder-Policy","require-corp");
  res.setHeader("Cross-Origin-Resource-Policy","same-origin");res.setHeader("Cache-Control","no-store");
  const url=new URL(req.url,"http://localhost"),name=url.pathname==="/"?"index.html":url.pathname.slice(1);
  let file;
  if(name.startsWith("bundle/")&&files.has(name.slice(7)))file=path.join(bundle,name.slice(7));
  else if(publicFiles.has(name))file=path.join(publicRoot,name);
  if(!file||!fs.existsSync(file)||!["GET","HEAD"].includes(req.method)){res.writeHead(404);res.end("Not found");return;}
  res.setHeader("Content-Type",types[path.extname(file)]||"application/octet-stream");res.setHeader("Content-Length",fs.statSync(file).size);
  if(req.method==="HEAD")res.end();else fs.createReadStream(file).on("error",()=>res.destroy()).pipe(res);
});
server.on("error",error=>{
  console.error(error.code==="EADDRINUSE"?`Port ${port} is in use. Choose another port: tools/gpt2-packed serve ${port+1}`:error.message);
  process.exitCode=1;
});
server.listen(port,"127.0.0.1",()=>console.log(`Packed GPT-2 browser: http://127.0.0.1:${server.address().port}`));
