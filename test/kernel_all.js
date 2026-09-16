#!/usr/bin/env node
// Focused PoC suite. Run directly: each child serializes its own Lean calls.
const {runChecked}=require("../tools/run-process");
for(const name of ["sort","universe","graph","binding","infer","pi","check",
  "substitution","application","conversion","let","export","proofs"]){
  const result=runChecked([process.execPath,`test/kernel_${name}.js`],{encoding:"utf8",timeout:900000});
  process.stdout.write(result.stdout);
}
const composition=runChecked([process.execPath,"test/kernel_export.js","composition"],{encoding:"utf8",timeout:900000});
process.stdout.write(composition.stdout);
console.log("all kernel PoC execution, export, and source-proof gates passed");
