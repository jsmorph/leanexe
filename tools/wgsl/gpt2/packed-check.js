#!/usr/bin/env node
"use strict";
// Parse the experimental Wasm independently with Talos, then check that its
// real wrapper/allocator declarations satisfy the proved QKV call theorem.
const fs=require("node:fs"),path=require("node:path");
const {spawnSync}=require("node:child_process");
const {spawnResultAsync}=require("../../run-process");
const {normalizeExpandedProgram}=require("../../talos-lib");
const {lean,audit}=require("../package");
const root=path.resolve(__dirname,"../../..");
const proofRoot=path.join(root,"proofs/talos/lean");
const write=(file,text)=>fs.writeFileSync(file,text,{flag:"wx"});
async function check(wasm,shaders,attempt) {
  wasm=path.resolve(wasm);shaders=path.resolve(shaders);attempt=path.resolve(attempt);
  fs.mkdirSync(attempt,{recursive:true});
  const name="gpt2_packed_runtime",namespace="Project.Gpt2PackedRuntime";
  const crate=path.join(attempt,"rust",name),stage=path.join(attempt,"rust/build",name);
  fs.mkdirSync(crate,{recursive:true});fs.mkdirSync(stage,{recursive:true});
  write(path.join(crate,"Cargo.toml"),`[package]\nname = "${name}"\nversion = "0.0.0"\nedition = "2021"\n`);
  fs.copyFileSync(wasm,path.join(stage,"program.wasm"),fs.constants.COPYFILE_EXCL);
  const parsed=spawnSync(process.env.WASM_TOOLS||"wasm-tools",["print",wasm,"-o",path.join(stage,"program.wat")],{stdio:"inherit"});
  if(parsed.error||parsed.status!==0)throw Error("cannot read hybrid Wasm");
  const verifier=path.join(proofRoot,".lake/packages/CodeLib/verifier/.lake/build/bin/verifier");
  const emitted=await spawnResultAsync([path.join(root,"tools/leanrun"),"--timeout","120s",verifier,"emit","--force-emit","--expanded",name],
    {cwd:attempt,env:process.env,stdio:["ignore","pipe","pipe"]});
  write(path.join(attempt,"emit.log"),emitted.stdout.toString()+emitted.stderr.toString());
  if(emitted.status!==0)throw Error(`Talos emission failed: ${attempt}/emit.log`);
  const source=fs.readFileSync(path.join(attempt,"lean/Project/Gpt2PackedRuntime/Program.lean"),"utf8");
  const normalized=normalizeExpandedProgram(source,name);
  const theorem=`${namespace}.checkedQkv`;
  const generated=path.join(attempt,"Check.lean");
  write(generated,normalized.replace("import Project.TalosPrelude","import Project.TalosPrelude\nimport Project.Gpt2.PackedWrapper")+"\n"+
    fs.readFileSync(path.join(shaders,"qkv/source-equality.lean.txt"),"utf8")+`\n
namespace ${namespace}
open Wasm
def checkedQkv (env : HostEnv Unit) (imp : ImportDecl) (host : HostFn Unit)
    (hImp : «module».imports[0]? = some imp) (hHost : env.funcs[0]? = some host)
    (hParams : imp.params = List.replicate 12 .i64) (hResults : imp.results = []) :=
  Project.Gpt2.PackedWrapper.qkv_exact «module» env rfl rfl rfl rfl rfl
    imp host hImp hHost hParams hResults _ LeanExe.WGSL.Gpt2Packed.qkv.wgslExecutionCorrect
#print axioms checkedQkv
end ${namespace}
`);
  await lean("packed wrapper dependencies",["lake","-d",proofRoot,"build","Project.Gpt2.PackedWrapper"],path.join(attempt,"dependencies.log"));
  const output=await lean("actual hybrid module QKV wrapper",["lake","-d",proofRoot,"env","lean",generated],path.join(attempt,"check.log"));
  const axioms=audit(output,[theorem]);
  write(path.join(attempt,"results.json"),JSON.stringify({status:"pass",theorem,axioms,
    subject:"actual hybrid QKV wrapper allocation, completed shader transfer and parent packed output",
    hostAssumption:"synchronous invocation copies the modeled shader result and preserves all other store fields",
    fullHybridSessionProved:false,universalWebGPUConformanceProved:false},null,2)+"\n");
  console.log(`Checked actual QKV wrapper: ${attempt}`);
}
if(require.main===module) {
  const args=process.argv.slice(2);
  if(args.length!==3)throw Error("usage: packed-check.js MODEL.wasm CHECKED_SHADERS FRESH_ATTEMPT");
  check(...args).catch(error=>{console.error(error.message);process.exitCode=1;});
}
module.exports={check};
