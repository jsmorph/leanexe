#!/usr/bin/env node
"use strict";
// Build the packed artifacts from source and check their hybrid controller.
// The tokenizer, sampler and conversion adapter remain separate proof scopes.
const fs=require("node:fs"),path=require("node:path");
const {spawnResultAsync}=require("../../run-process");
const {generate}=require("./packed-shaders"),{check}=require("./packed-check"),{compose}=require("./packed-compose");
const root=path.resolve(__dirname,"../../.."),proofRoot=path.join(root,"proofs/talos/lean");
async function build(destination,proofCache){
  destination=path.resolve(destination);if(fs.existsSync(destination))throw Error("build destination must be fresh");
  if(/[\r\n]/.test(destination))throw Error("build path cannot contain a newline");
  fs.mkdirSync(destination,{recursive:true});
  const logs=path.join(destination,"logs"),bundle=path.join(destination,"bundle");
  fs.mkdirSync(logs);fs.mkdirSync(bundle);
  const record={status:"running",steps:[],proofScope:"FP32 cached-step and token-list session under declared WebGPU host execution/transfer assumptions"};
  const save=()=>fs.writeFileSync(path.join(destination,"build.json"),JSON.stringify(record,null,2)+"\n");save();
  async function run(name,args){
    console.log(`Packed build: ${name}`);
    const result=await spawnResultAsync(args,{cwd:root,env:process.env,stdio:["ignore","pipe","pipe"]});
    fs.writeFileSync(path.join(logs,name+".log"),result.stdout.toString()+result.stderr.toString(),{flag:"wx"});
    if(result.status!==0)throw Error(`${name} failed: ${logs}/${name}.log`);
    record.steps.push(name);save();
  }
  const runner=path.join(root,"tools/leanrun"),source=path.join(root,"build/gpt2/source");
  const python=process.env.GPT2_BUILD_PYTHON||path.join(root,"build/gpt2/venv/bin/python");
  try{
    if(!fs.existsSync(python))throw Error("Build Python is missing; create build/gpt2/venv with requirements-build.txt, or set GPT2_BUILD_PYTHON");
    await run("checkpoint",[python,path.join(__dirname,"download.py"),source]);
    await run("assets",[python,path.join(__dirname,"packed-assets.py"),source,bundle]);
    await run("parent-proof",[path.join(root,"tools/talos-proof.js"),"check","gpt2_cached_step"]);
    const runtime=path.join(destination,"runtime"),shaders=path.join(destination,"shaders"),wrappers=path.join(destination,"wrappers");
    await run("hybrid-wasm",[process.execPath,path.join(__dirname,"packed-module.js"),
      path.join(root,"proofs/talos/.generated/gpt2_cached_step/program.wat"),runtime]);
    await generate(shaders);
    await check(path.join(runtime,"model.wasm"),shaders,wrappers);
    const proof=proofCache?path.resolve(proofCache):path.join(destination,"proof");
    await compose(path.join(wrappers,"lean/Project/Gpt2PackedRuntime/Program.lean"),shaders,proof,
      {resume:!!proofCache&&fs.existsSync(proof)});
    await run("auxiliary-source",[runner,"--timeout","120s","lake","-d",proofRoot,"build","Project.Gpt2.Model","Project.Gpt2.Tokenizer"]);
    for(const [module,entry,name] of [["Project.Gpt2.Model","Project.Gpt2.compute","sampler"],
      ["Project.Gpt2.Tokenizer","Project.Gpt2.Tokenizer.tokens","tokenizer"]])
      await run(name,[runner,"--timeout","120s","lake","-d",proofRoot,"env",path.join(root,".lake/build/bin/lean-wasm"),
        "compile","--module",module,"--entry",entry,"--out",path.join(bundle,name+".wasm")]);
    await run("conversion-source",[python,path.join(__dirname,"transfer.py"),path.join(destination,"transfer.wat")]);
    await run("conversion-wasm",[process.env.WASM_TOOLS||"wasm-tools","parse",path.join(destination,"transfer.wat"),"-o",path.join(bundle,"transfer.wasm")]);
    fs.copyFileSync(path.join(runtime,"model.wasm"),path.join(bundle,"model.wasm"));
    for(const name of ["model","sampler","tokenizer","transfer"])
      await run(`validate-${name}`,[process.env.WASM_TOOLS||"wasm-tools","validate",path.join(bundle,name+".wasm")]);
    for(const role of ["qkv","attention","expansion","projection","vocabularyLeft","vocabularyRight"]){
      const out=path.join(bundle,"shaders",role);fs.mkdirSync(out,{recursive:true});
      fs.copyFileSync(path.join(shaders,role,"kernel.wgsl"),path.join(out,"kernel.wgsl"));
    }
    await run("native-host",[path.join(__dirname,"compile-packed-host.sh")]);
    const manifest={format:"leanexe-gpt2-packed-v1",contextTokens:128,parameters:124439808,
      algorithm:"LeanExe.Models.Gpt2.cachedStep",stepTheorem:"Project.Gpt2Hybrid.Spec.cachedStep_exact",
      sessionTheorem:"Project.Gpt2Hybrid.Spec.gpt2_128_exact",proofDirectory:proof,
      assumptions:"The host completes the certified shader execution with the declared separate FP32 operations and copies only output bytes; successful native/browser allocation and driver execution are external assumptions.",
      outsideProofScope:["tokenizer","token selection/sampling","FP32-to-FP64 sampling adapter","native and browser host implementation","universal WebGPU driver conformance"],
      arithmetic:"Packed FP32 Wasm controller with compiled WGSL matrix calls; tokenizer and sampling arithmetic in Wasm"};
    fs.writeFileSync(path.join(bundle,"manifest.json"),JSON.stringify(manifest,null,2)+"\n");
    record.status="pass";record.bundle=bundle;record.proofDirectory=proof;save();
    const current=path.join(root,"build/gpt2/packed-current");
    fs.writeFileSync(current+".partial",bundle+"\n");fs.renameSync(current+".partial",current);
    console.log(`Built and checked packed model: ${bundle}`);
  }catch(error){record.status="failed";record.error=error.message;save();throw error;}
}
if(require.main===module){
  const args=process.argv.slice(2),at=args.indexOf("--proof-cache"),cache=at<0?null:args[at+1];if(at>=0)args.splice(at,2);
  if(args.length!==1||at>=0&&!cache)throw Error("usage: packed-build.js FRESH_OUTPUT_DIRECTORY [--proof-cache CHECKED_PROOF_CACHE]");
  build(args[0],cache).catch(error=>{console.error(error.message);process.exitCode=1;});
}
module.exports={build};
