#!/usr/bin/env node
"use strict";

// Experimental integration artifact. The parent proof does not automatically
// transfer to this changed module. Wrapper/call/session proofs are separate gates.
const fs = require("node:fs");
const path = require("node:path");
const {spawnSync} = require("node:child_process");
function transform(source) {
  if (/\(import\b|call_indirect|return_call|ref\.func|\(elem\b|\(start\b/.test(source))
    throw Error("unsupported parent module syntax");
  const starts = [...source.matchAll(/^  \(func \(;([0-9]+);\)/gm)];
  if (starts.length !== 43 || starts.some((m,i)=>Number(m[1])!==i))
    throw Error("expected the reviewed 43-function parent module");
  let prefix = source.slice(0, starts[0].index);
  const functions = starts.map((m,i)=>source.slice(m.index, i+1<starts.length?starts[i+1].index:source.lastIndexOf(")")));
  const gets = count => Array.from({length:count},(_,i)=>`    local.get ${i}`).join("\n");
  functions[21] = `  (func (;21;) (type 21) (param ${Array(11).fill("i64").join(" ")}) (result i64 i64 i64)
    (local i64)
    local.get 9
    i64.const 4
    i64.mul
    call 39
    local.set 11
${gets(12)}
    call $packed_linear
    local.get 11
    local.get 11
    local.get 9
    i64.const 4
    i64.mul)
`;
  functions[37] = `  (func (;37;) (type 37) (param ${Array(6).fill("i64").join(" ")}) (result i64 i64 i64)
    (local i64)
    i64.const 201028
    call 39
    local.set 6
${gets(7)}
    call $packed_vocabulary
    local.get 6
    local.get 6
    i64.const 201028)
`;
  prefix = prefix.replace(/\(func (\d+)\)/g,(_,n)=>`(func ${Number(n)+2})`);
  const imports = `  (import "wgsl" "linear" (func $packed_linear (param ${Array(12).fill("i64").join(" ")})))
  (import "wgsl" "vocabulary" (func $packed_vocabulary (param ${Array(7).fill("i64").join(" ")})))
`;
  prefix = prefix.replace("  (memory", imports+"  (memory");
  return prefix+functions.map(f=>f.replace(/\bcall (\d+)\b/g,(_,n)=>`call ${Number(n)+2}`)
    .replace(/^  \(func \(;(\d+);\)/,(_,n)=>`  (func (;${Number(n)+2};)`)).join("")+")\n";
}
module.exports = {transform};
if (require.main === module) {
  const [input,output] = process.argv.slice(2);
  if (!input || !output) throw Error("usage: packed-module.js PARENT.wat FRESH_OUTPUT_DIRECTORY");
  fs.mkdirSync(output,{recursive:true});
  const wat = path.join(output,"model.wat"), wasm = path.join(output,"model.wasm");
  fs.writeFileSync(wat,transform(fs.readFileSync(input,"utf8")),{flag:"wx"});
  for (const args of [["parse",wat,"-o",wasm],["validate",wasm]]) {
    const p=spawnSync(process.env.WASM_TOOLS||"wasm-tools",args,{stdio:"inherit"});
    if (p.error||p.status!==0) throw Error("Wasm assembly/validation failed");
  }
  console.log("Created experimental packed FP32 hybrid module; full hybrid execution proof pending.");
}
