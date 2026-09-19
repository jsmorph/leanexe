#!/usr/bin/env node
"use strict";
// Check semantic transport for the unchanged closed helper region in the
// independently parsed hybrid module. Does not include the three controllers.
const fs=require("node:fs"),path=require("node:path");
const {normalizeExpandedProgram}=require("../../talos-lib");
const {lean,audit}=require("../package");
const root=path.resolve(__dirname,"../../..");
const proofRoot=path.join(root,"proofs/talos/lean");
async function check(emitted,attempt) {
  emitted=path.resolve(emitted);attempt=path.resolve(attempt);fs.mkdirSync(attempt,{recursive:true});
  const program=normalizeExpandedProgram(fs.readFileSync(emitted,"utf8"),"gpt2_packed_runtime");
  const ids=Array.from({length:43},(_,i)=>i).filter(i=>![21,33,36,37,38].includes(i));
  const declarations=ids.flatMap(i=>[
    `theorem portable${i} : PortableProgram helperDomain Project.Gpt2CachedStep.func${i} := by`,
    `  unfold Project.Gpt2CachedStep.func${i}`,
    `  repeat' (first | decide | constructor)`,
    `theorem function${i} : func${i}Def = renameFunction (· + 2) id Project.Gpt2CachedStep.func${i}Def := by rfl`,
  ]);
  const names=["Project.Gpt2PackedRuntime.helpers","Project.Gpt2PackedRuntime.helper_correct"];
  const file=path.join(attempt,"Helpers.lean");
  fs.writeFileSync(file,program.replace("import Project.TalosPrelude",
    "import Project.TalosPrelude\nimport Project.FunctionRegion.Imports\nimport Project.Gpt2CachedStep.Program")+`\n
namespace Project.Gpt2PackedRuntime
open Wasm Project.FunctionRegion
def helperDomain (i : Nat) : Prop := i ∈ [${ids.join(",")}]
instance (i : Nat) : Decidable (helperDomain i) := inferInstanceAs (Decidable (i ∈ _))
${declarations.join("\n")}
theorem helpers : ImportShift Project.Gpt2CachedStep.«module» «module» (· + 2) id helperDomain := by
  refine ⟨rfl, ?_⟩
  intro i hi
  simp [helperDomain] at hi
  rcases hi with ${ids.map(()=>"rfl").join(" | ")}
${ids.map(i=>`  · exact ⟨_, rfl, rfl, rfl, congrArg some function${i}, portable${i}⟩`).join("\n")}
theorem helper_correct (env : HostEnv Unit) (i : Nat) (hi : helperDomain i)
    (initial : Store Unit) (args : List Value) (post : Store Unit → List Value → Prop)
    (original : TerminatesWith env Project.Gpt2CachedStep.«module» i initial args post) :
    TerminatesWith env «module» (i + 2) initial args post :=
  WithImports.terminatesWith helpers i hi original
${names.map(n=>`#print axioms ${n}`).join("\n")}
end Project.Gpt2PackedRuntime
`,{flag:"wx"});
  await lean("host-import region transport dependencies",["lake","-d",proofRoot,"build","Project.FunctionRegion.Imports"],path.join(attempt,"dependencies.log"));
  const output=await lean("unchanged hybrid Wasm helpers",["lake","-d",proofRoot,"env","lean",file],path.join(attempt,"helpers.log"));
  fs.writeFileSync(path.join(attempt,"results.json"),JSON.stringify({status:"pass",functionIndices:ids,axioms:audit(output,names),
    fullHybridSessionProved:false},null,2)+"\n",{flag:"wx"});
  console.log(`Checked ${ids.length} unchanged functions under the hybrid module's imports.`);
}
if(require.main===module) {
  const args=process.argv.slice(2);
  if(args.length!==2)throw Error("usage: packed-regions.js EMITTED_PROGRAM.lean FRESH_ATTEMPT");
  check(...args).catch(error=>{console.error(error.message);process.exitCode=1;});
}
module.exports={check};
