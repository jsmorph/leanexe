#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const { dataset, expectedWords, decode, compareNumerics, buildDataset, publish } =
  require("../tools/euler-rusanov-step-data");

assert.deepEqual(decode(0n), [0n,1n]);
assert.deepEqual(decode(0x8000000000000000n), [0n,1n]);
assert.deepEqual(decode(0x3ff0000000000000n), [1n,1n]);
assert.deepEqual(decode(0xbff0000000000000n), [-1n,1n]);
assert.deepEqual(decode(0x3fb999999999999an), [3602879701896397n,36028797018963968n]);
assert.deepEqual(decode(1n), [1n,1n << 1074n]);
for(const bad of [-1n,1n<<64n,0x7ff0000000000000n,0x7ff8000000000000n])
  assert.throws(() => decode(bad));
const checked=compareNumerics([...expectedWords]);
assert.deepEqual(checked.residual,[[0n,1n],[1n,1n<<57n],[-1n,1n<<56n]]);
for(let i=0;i<expectedWords.length;++i) {
  const changed=[...expectedWords]; changed[i]+=1n;
  assert.throws(()=>compareNumerics(changed));
}
const built=buildDataset();
publish(built,false);
assert.equal(built.files.get(`${dataset}.csv`).trimEnd().split("\n").length,3);
assert.equal(built.files.get("exact-comparison.csv").trimEnd().split("\n").length,7);
assert.equal(built.files.get("presentation.csv").trimEnd().split("\n").length,3);
for(const contents of built.files.values()) {
  assert.equal(contents.includes("\r"),false);
  assert.ok(contents.endsWith("\n"));
}
const manifest=JSON.parse(built.files.get("manifest.json"));
assert.deepEqual(manifest.exactDecodedBalanceResidual,["0","1/144115188075855872","-1/72057594037927936"]);
console.log("checked fixed-step frozen words, canonical raw data, rational errors, signed-zero/subnormal decoding, nonfinite rejection, and presentation artifacts");
