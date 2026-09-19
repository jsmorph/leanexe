#!/usr/bin/env node
"use strict";

// Compile supported Lean bodies, then apply their certificates to the parent's
// packed FP32 source. Generated text, proof fragments and receipts stay in build/.
const fs = require("node:fs");
const path = require("node:path");
const {spawnSync} = require("node:child_process");
const {lean, audit} = require("../package");
const root = path.resolve(__dirname, "../../..");
const proofRoot = path.join(root, "proofs/talos/lean");
const write = (file, text) => fs.writeFileSync(file, text, {flag:"wx"});
const plan = [
  ["qkv",768,2304,true], ["attention",768,768,true], ["expansion",768,3072,true],
  ["projection",3072,768,true], ["vocabularyLeft",768,25129,false], ["vocabularyRight",768,25128,false],
].map(([role,inner,cols,bias], index) => ({role,inner,cols,bias,index,
  elementsB:inner*cols+(bias?cols:0), source:`LeanExe.WGSL.${bias?"Gpt2Packed":"Gpt2"}.${role}`}));

async function generate(directory) {
  directory = path.resolve(directory);
  fs.mkdirSync(directory, {recursive:true});
  await lean("parent packed shader connections", ["lake","-d",proofRoot,"build","Project.Gpt2.PackedShader"],
    path.join(directory,"dependencies.log"));
  const results = [];
  for (const item of plan) {
    const {role,inner,cols,elementsB,source,bias} = item;
    const destination = path.join(directory,role);
    const file = path.join(directory,`${role}.lean`);
    const suffixes = ["wgslSourceCorrect","wgslShaderParsed","wgslExecutionCorrect"];
    const connections = bias ? [
      `def ${source}.parentColumn (weights input : ByteArray) (weightOffset biasOffset col : Nat)`,
      `  (hc : col < ${cols}) := Project.Gpt2.PackedBody.biasedColumn_exact`,
      `  _ ${inner} ${cols} ${source}.wgslExecutionCorrect weights input weightOffset biasOffset col hc (by decide)`,
      `def ${source}.parentBytes (weights input : ByteArray) (weightOffset biasOffset : Nat) :=`,
      `  Project.Gpt2.PackedBody.biasedBytes_exact _ ${inner} ${cols} ${source}.wgslExecutionCorrect`,
      `    weights input weightOffset biasOffset (by decide)`,
    ] : [];
    if (bias) suffixes.push("parentColumn","parentBytes");
    write(file,["import Project.Gpt2.PackedShader",
      `#compile_wgsl ${source} 1 ${cols} ${inner} ${elementsB} ${JSON.stringify(destination)}`,
      ...connections, ...suffixes.map(s=>`#print axioms ${source}.${s}`),""].join("\n"));
    const output = await lean(`compile packed FP32 ${role}`, ["lake","-d",proofRoot,"env","lean",file],
      path.join(directory,`${role}.log`));
    results.push({...item,package:destination,axioms:audit(output,suffixes.map(s=>`${source}.${s}`))});
  }
  const left = results[4], right = results[5];
  const vocabulary = "Project.Gpt2.CheckedParentVocabulary";
  const replay = path.join(directory,"vocabulary.lean");
  write(replay,["import Project.Gpt2.PackedShader",
    ...[left,right].map(item=>fs.readFileSync(path.join(item.package,"source-equality.lean.txt"),"utf8")),
    `def ${vocabulary} := Project.Gpt2.PackedBody.vocabularyBytes_exact _ _`,
    `  ${left.source}.wgslExecutionCorrect ${right.source}.wgslExecutionCorrect`,
    `#print axioms ${vocabulary}`,""].join("\n"));
  const output = await lean("packed parent vocabulary composition",
    ["lake","-d",proofRoot,"env","lean",replay],path.join(directory,"vocabulary.log"));
  const receipt = {status:"pass",subject:"compiled shader execution to parent packed FP32 source",
    results,vocabulary:{theorem:vocabulary,axioms:audit(output,[vocabulary])},
    fullHybridWasmExecutionProved:false, universalWebGPUConformanceProved:false};
  write(path.join(directory,"results.json"),JSON.stringify(receipt,null,2)+"\n");
  return receipt;
}
async function test(directory, existing = false) {
  directory = path.resolve(directory);
  if (!existing) await generate(directory);
  else if (JSON.parse(fs.readFileSync(path.join(directory,"results.json"),"utf8")).status !== "pass")
    throw Error("existing shader certificate gate did not pass");
  const attempt = fs.mkdtempSync(path.join(directory,"cpu-test-"));
  const file = path.join(attempt,"small.lean");
  const name = "PackedBiasedSmall";
  const suffixes = ["wgslSourceCorrect","wgslShaderParsed","wgslExecutionCorrect"];
  write(file,["import Project.Gpt2.PackedShader",
    `@[wgsl] def ${name} : LeanExe.WGSL.Source.Kernel := fun ar a b row col => LeanExe.WGSL.Gpt2Packed.biased 3 2 ar a b row col`,
    `#compile_wgsl ${name} 1 2 3 8 ${JSON.stringify(path.join(directory,"small"))}`,
    ...suffixes.map(s=>`#print axioms ${name}.${s}`),""].join("\n"));
  const checked = await lean("small biased kernel",["lake","-d",proofRoot,"env","lean",file],
    path.join(attempt,"small.log"));
  audit(checked,suffixes.map(s=>`${name}.${s}`));
  await lean("packed shader expected words from Lean",["lake","-d",proofRoot,"env","lean","--run",
    path.join(__dirname,"PackedVectors.lean"),path.join(directory,"vectors")],path.join(attempt,"vectors.log"));
  const executed = spawnSync(path.join(root,"tools/wgsl/run-macos-cpu.sh"),["--gpt2-packed",directory],
    {cwd:root,env:process.env,encoding:"utf8",maxBuffer:1024*1024});
  write(path.join(attempt,"execution.log"),(executed.stdout||"")+(executed.stderr||""));
  if (executed.error || executed.status !== 0) throw Error(`Packed CPU test failed: ${attempt}/execution.log`);
  process.stdout.write(executed.stdout);
}
module.exports = {plan,generate,test};
if (require.main === module) {
  if (process.argv.length < 3 || process.argv.length > 4 ||
      (process.argv.length === 4 && !["--test","--test-existing"].includes(process.argv[3])))
    throw Error("usage: packed-shaders.js DIRECTORY [--test|--test-existing]");
  (process.argv[3] ? test(process.argv[2],process.argv[3] === "--test-existing") : generate(process.argv[2]))
    .then(()=>console.log("Six shaders connected to the parent packed FP32 source."))
    .catch(error=>{console.error(error.message);process.exitCode=1;});
}
