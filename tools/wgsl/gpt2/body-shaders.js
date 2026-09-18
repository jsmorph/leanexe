#!/usr/bin/env node
"use strict";

// Compile the six Lean definition bodies, or check existing shader texts against
// those same definitions. All arithmetic remains in Lean/WGSL; this is build glue.
const fs = require("node:fs");
const path = require("node:path");
const {lean, audit} = require("../package");
const root = path.resolve(__dirname, "../../..");
const proofRoot = path.join(root, "proofs/talos/lean");
const plan = [
  ["qkv",768,2304], ["attention",768,768], ["expansion",768,3072],
  ["projection",3072,768], ["vocabularyLeft",768,25129], ["vocabularyRight",768,25128],
].map(([role,inner,cols], index) => ({role,inner,cols,index,shader:`kernel-${index}.wgsl`}));
const write = (file, text) => fs.writeFileSync(file, text, {flag:"wx"});

async function dependencies(attempt) {
  await lean("body compiler and GPT-2 specification", ["lake", "-d", proofRoot, "build", "Project.Gpt2.BodyCompile"],
    path.join(attempt,"dependencies.log"));
}
async function one(item, attempt, existing = null) {
  const {role,inner,cols,index,shader} = item;
  const name = `LeanExe.WGSL.Gpt2.${role}`;
  const destination = path.join(attempt, String(index));
  const input = existing === null ? "" : `${JSON.stringify(existing)} `;
  const command = existing === null ? "#compile_wgsl" : "#check_wgsl";
  const file = path.join(attempt, `${role}.lean`);
  const code = [
    "import Project.Gpt2.BodyCompile",
    `${command} ${name} 1 ${cols} ${inner} ${inner*cols} ${input}${JSON.stringify(destination)}`,
    // This proof specializes the checked statement execution to the established
    // packed matrix specification, including its concrete binary32 arithmetic.
    `def ${name}.wgslGpt2Product := Project.Gpt2.Matrix.from_body_shader .${role}`,
    `  _ ${name}.wgslExecutionCorrect`,
    ...["wgslSourceCorrect","wgslShaderParsed","wgslExecutionCorrect","wgslGpt2Product"]
      .map(suffix => `#print axioms ${name}.${suffix}`), "",
  ].join("\n");
  write(file, code);
  const output = await lean(`GPT-2 ${existing ? "check" : "compile"} Lean body: ${role}`,
    ["lake", "-d", proofRoot, "env", "lean", file], path.join(attempt,`${role}.log`));
  const axioms = audit(output, ["wgslSourceCorrect","wgslShaderParsed","wgslExecutionCorrect","wgslGpt2Product"]
    .map(suffix=>`${name}.${suffix}`));
  return {role,shader,inner,cols,package:destination,sourceDeclaration:name,axioms};
}
async function checkVocabulary(attempt, results) {
  const heads = ["vocabularyLeft", "vocabularyRight"].map(role => {
    const item = results.find(result => result.role === role);
    if (!item) throw Error(`Missing vocabulary shader: ${role}`);
    return {
      source: item.sourceDeclaration,
      text: fs.readFileSync(path.join(item.package,"kernel.wgsl"),"utf8"),
      proof: fs.readFileSync(path.join(item.package,"source-equality.lean.txt"),"utf8"),
    };
  });
  const name = "Project.Gpt2.CheckedVocabularyBodies";
  const file = path.join(attempt,"vocabulary.lean");
  write(file, ["import Project.Gpt2.BodyCompile", ...heads.map(head=>head.proof),
    `theorem ${name} (x embedding : LeanExe.WGSL.WordBuffer) (token : Nat) (ht : token < 50257) :`,
    `  Project.Gpt2.Matrix.vocabularyBodyRun ${JSON.stringify(heads[0].text)} ${JSON.stringify(heads[1].text)}`,
    "    x embedding token = Except.ok (some ⟨token, Project.Gpt2.Matrix.vocabulary x embedding token⟩) :=",
    "  Project.Gpt2.Matrix.vocabulary_from_body_shaders _ _",
    `    ${heads[0].source}.wgslExecutionCorrect ${heads[1].source}.wgslExecutionCorrect x embedding token ht`,
    `#print axioms ${name}`, ""].join("\n"));
  const output = await lean("GPT-2 body shader vocabulary composition",
    ["lake", "-d", proofRoot, "env", "lean", file], path.join(attempt,"vocabulary.log"));
  return {theorem:name, semantics:"Project.Gpt2.Matrix.vocabularyBodyRun", axioms:audit(output,[name])};
}
async function generate(attempt) {
  attempt = path.resolve(attempt);
  fs.mkdirSync(attempt, {recursive:true});
  await dependencies(attempt);
  const results = [];
  for (const item of plan) results.push(await one(item, attempt));
  const vocabulary = await checkVocabulary(attempt, results);
  write(path.join(attempt,"results.json"), JSON.stringify({status:"pass",kind:"lean-body-wgsl",results,vocabulary},null,2)+"\n");
  return results;
}
async function checkExisting(directory, attempt, snapshots) {
  const selected = path.join(attempt,"body-compiler");
  fs.mkdirSync(selected);
  await dependencies(selected);
  const results = [];
  for (const item of plan) {
    const snapshot = path.join(selected,item.shader);
    write(snapshot,snapshots[item.index]);
    results.push(await one(item,selected,snapshot));
  }
  return {results, vocabulary:await checkVocabulary(selected, results)};
}
module.exports = {plan,generate,checkExisting};
if (require.main === module) {
  if (process.argv.length !== 3) throw Error("usage: body-shaders.js FRESH_GENERATION_DIRECTORY");
  generate(process.argv[2]).then(results => console.log(`Compiled and proved ${results.length} GPT-2 shader bodies.`))
    .catch(error=>{console.error(error.message);process.exitCode=1;});
}
