#!/usr/bin/env node
"use strict";
// Assemble existing generated artifacts for the experimental packed runner.
// Does not create or assert a full hybrid session proof.
const fs=require("node:fs"),path=require("node:path");
const root=path.resolve(__dirname,"../../..");
const [runtime,shaders,destination]=process.argv.slice(2).map(x=>path.resolve(x));
if(!runtime||!shaders||!destination)throw Error("usage: prepare-packed.js RUNTIME_DIRECTORY CHECKED_SHADERS FRESH_BUNDLE");
if(fs.existsSync(destination))throw Error("bundle must be new");
const receipt=JSON.parse(fs.readFileSync(path.join(shaders,"results.json"),"utf8"));
if(receipt.status!=="pass"||receipt.results.length!==6)throw Error("six shader certificates required");
fs.mkdirSync(destination,{recursive:true});
const copy=(source,name)=>fs.copyFileSync(source,path.join(destination,name),fs.constants.COPYFILE_EXCL);
copy(path.join(runtime,"model.wasm"),"model.wasm");
const previous=path.join(root,"build/gpt2/bundle");
for(const [from,to] of [["model.wasm","sampler.wasm"],["tokenizer.wasm","tokenizer.wasm"],
  ["tokenizer.bin","tokenizer.bin"],["transfer.wasm","transfer.wasm"]])copy(path.join(previous,from),to);
fs.symlinkSync(path.join(root,"build/gpt2/source/inference/weights.bin"),path.join(destination,"weights.bin"));
for(const result of receipt.results) {
  const target=path.join(destination,"shaders",result.role);fs.mkdirSync(target,{recursive:true});
  fs.copyFileSync(path.join(shaders,result.role,"kernel.wgsl"),path.join(target,"kernel.wgsl"),fs.constants.COPYFILE_EXCL);
}
fs.writeFileSync(path.join(destination,"manifest.json"),JSON.stringify({format:"leanexe-gpt2-packed-experimental-v1",
  contextTokens:128,fullHybridSessionProved:false,shaderCertificates:receipt,
  arithmetic:"parent packed FP32 non-matrix Wasm; compiled FP32 WGSL products; Wasm tokenizer and sampler"},null,2)+"\n");
console.log(destination);
