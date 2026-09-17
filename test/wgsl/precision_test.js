"use strict";

const assert = require("node:assert/strict");
const path = require("node:path");
const { runChecked } = require("../../tools/run-process");
const corpus = require("./precision-vectors.json");
const root = path.resolve(__dirname, "../..");
const proofRoot = path.join(root, "proofs/talos/lean");

runChecked(["lake", "-d", proofRoot, "build", "Project.WGSL.Precision"],
  { cwd: root, timeout: 60000, encoding: "utf8" });
for (const direction of ["promote", "demote"]) {
  const cases = corpus[direction];
  const output = runChecked(["lake", "-d", proofRoot, "env", "lean", "--run",
    path.join(root, "tools/wgsl/PrecisionModel.lean"), direction,
    ...cases.map(row => BigInt(`0x${row.input}`).toString())],
  { cwd: root, timeout: 60000, encoding: "utf8" }).stdout.trim().split(/\s+/).map(BigInt);
  assert.equal(output.length, cases.length);
  cases.forEach((row, index) => {
    const bytes = Buffer.alloc(8);
    let native;
    if (direction === "promote") {
      bytes.writeUInt32LE(Number(BigInt(`0x${row.input}`)));
      const value = bytes.readFloatLE();
      bytes.writeDoubleLE(value);
      native = bytes.readBigUInt64LE();
    } else {
      bytes.writeBigUInt64LE(BigInt(`0x${row.input}`));
      const value = bytes.readDoubleLE();
      bytes.writeFloatLE(value);
      native = BigInt(bytes.readUInt32LE());
    }
    const expected = BigInt(`0x${row.expected}`);
    assert.equal(output[index], expected, `${direction}: pure model: ${row.name}`);
    assert.equal(native, expected, `${direction}: native conversion: ${row.name}`);
  });
  console.log(`Checked ${cases.length} ${direction} boundary vectors against the pure model and native conversion`);
}
