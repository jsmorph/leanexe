#!/usr/bin/env node
"use strict";
const fs=require("node:fs");
const {decodeExport}=require("./kernel-export-format");
const {ensureHost,parseI64SlotsOutput}=require("./wasmtime-host");
const {runChecked}=require("./run-process");
function checkExportFile(wasm,file,fuel="10000") {
  if(!/^[0-9]+$/.test(String(fuel))||BigInt(fuel)>18446744073709551615n)throw new Error("fuel must be a UInt64 decimal");
  const decoded=decodeExport(fs.readFileSync(file,"utf8"));
  const result=runChecked([ensureHost(),"call",wasm,"checkExport","i64",
    `array-u64:${decoded.graph.join(",")}`,`i64:${decoded.term}`,`i64:${decoded.claimed}`,`i64:${fuel}`],
    {encoding:"utf8",timeout:30000});
  const status=Number(parseI64SlotsOutput("checkExport",1,result.stdout)[0]);
  const labels=["accepted","rejected","representation-overflow","unsupported","malformed","exhausted"];
  if(!labels[status])throw new Error(`unexpected checker status ${status}`);
  return {declaration:decoded.name,status,result:labels[status],globals:0,universeParameters:0,axioms:[]};
}
if(require.main===module){
  try{
    if(process.argv.length<4||process.argv.length>5)throw new Error("usage: node tools/kernel-check-export.js <checker.wasm> <proof.ndjson> [fuel]");
    const report=checkExportFile(process.argv[2],process.argv[3],process.argv[4]);
    console.log(JSON.stringify(report));
    process.exitCode=report.status===0?0:report.status===1?1:2;
  }catch(error){console.error(error.message);process.exitCode=2;}
}
module.exports={checkExportFile};
