#!/usr/bin/env node
"use strict";
// Preparation/reproducibility only; the runtime command does not load Lean.
const assert=require("node:assert/strict");
const fs=require("node:fs");
const path=require("node:path");
const {runChecked}=require("./run-process");
const root=path.resolve(__dirname,"..");
const exporter=path.join(root,"build/tools/lean4export");
const pin="483e011449cce37c3f8ad5e2aae434cbb1d2e53c";
function run(args){return runChecked(args,{cwd:root,encoding:"utf8",timeout:90000}).stdout;}
assert.equal(run(["git","-C",exporter,"rev-parse","HEAD"]).trim(),pin,"exporter revision");
assert.equal(run(["git","-C",exporter,"status","--porcelain"]).trim(),"","exporter checkout must be clean");
const fixture=process.argv[2] || "identity";
assert(["identity","composition","let"].includes(fixture),"known export fixture");
const moduleName=`LeanExe.KernelCheck.Fixtures.${{identity:"Identity",composition:"Composition",let:"Let"}[fixture]}`;
const declaration={identity:"implicationIdentity",composition:"implicationComposition",let:"implicationLet"}[fixture];
run(["lake","build",moduleName]);
const actual=run(["lake","env",path.join(exporter,".lake/build/bin/lean4export"),
  moduleName,"--",declaration]);
assert.equal(actual,fs.readFileSync(path.join(root,`test/fixtures/kernel-check/${fixture}.ndjson`),"utf8"),"fresh pinned-Lean export must equal frozen bytes");
console.log(`reproduced frozen ${declaration} export with lean4export ${pin}`);
