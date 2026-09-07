#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runChecked } = require("../tools/run-process");
const { callI64Slots } = require("../tools/wasmtime-host");
const moduleName = "LeanExe.Examples.Float64Bits";
const compiler = process.env.LEAN_WASM_EXE || path.join(".lake", "build", "bin", "lean-wasm");
const run = args => runChecked(args, { encoding: "utf8" }).stdout;
const isNaNBits = word => (word & 0x7ff0000000000000n) === 0x7ff0000000000000n &&
  (word & 0x000fffffffffffffn) !== 0n;
const one = 0x3ff0000000000000n, two = 0x4000000000000000n;
const negZero = 0x8000000000000000n, inf = 0x7ff0000000000000n;
const nan = 0x7ff8000000000000n, max = 0x7fefffffffffffffn;
const vectors = {
  subBits: [
    [[one, one], 0n], [[negZero, 0n], negZero], [[0n, negZero], 0n],
    [[0x0010000000000000n, 0x000fffffffffffffn], 1n],
    [[one, one - 1n], 0x3ca0000000000000n], [[1n, 1n], 0n],
    [[max, max | negZero], inf], [[inf, inf], "nan"],
    [[nan, one], "nan"], [[one, nan], "nan"],
  ],
  divBits: [
    [[one, two], 0x3fe0000000000000n],
    [[one, 0x4008000000000000n], 0x3fd5555555555555n],
    [[negZero, one], negZero], [[one, negZero], inf | negZero],
    [[0n, 0n], "nan"], [[inf, inf], "nan"], [[one, inf], 0n],
    [[0x0010000000000000n, two], 0x0008000000000000n],
    [[1n, two], 0n], [[3n, two], 2n], [[max, 0x3fe0000000000000n], inf],
    [[nan, one], "nan"], [[one, nan], "nan"],
  ],
  sqrtBits: [
    [[0n], 0n], [[negZero], negZero], [[0x4010000000000000n], two],
    [[two], 0x3ff6a09e667f3bcdn], [[1n], 0x1e60000000000000n],
    [[0x0010000000000000n], 0x2000000000000000n],
    [[one | negZero], "nan"], [[inf | negZero], "nan"], [[inf], inf],
    [[nan], "nan"], [[nan | negZero], "nan"],
  ],
  sqrtDivBits: [
    [[0x4022000000000000n, 0x4010000000000000n], 0x3ff8000000000000n],
    [[negZero, one], negZero], [[one | negZero, one], "nan"],
  ],
};

function instructions(wat, entry) {
  const match = wat.match(new RegExp(`\\(export "${entry}" \\(func (\\d+)\\)\\)`));
  assert.ok(match, `missing export ${entry}`);
  const marker = `(func (;${match[1]};)`;
  const start = wat.indexOf(marker), next = wat.indexOf("  (func (;", start + marker.length);
  assert.ok(start >= 0);
  const lines = wat.slice(start, next < 0 ? wat.length : next).trim().split(/\r?\n/).map(s => s.trim());
  assert.equal(lines.at(-1), ")");
  return lines.slice(1, -1).filter(s => !s.startsWith("(local"));
}

function main() {
  // Each regression invocation owns a fresh retained output directory.
  fs.mkdirSync("tmp", { recursive: true });
  const output = fs.mkdtempSync(path.join("tmp", "f64-extended-"));
  for (const entry of Object.keys(vectors)) {
    const args = ["--module", moduleName, "--entry", `${moduleName}.${entry}`];
    const wasm = path.join(output, `${entry}.wasm`), watFile = path.join(output, `${entry}.wat`);
    run([compiler, "compile", ...args, "--out", wasm]);
    run([compiler, "compile-wat", ...args, "--out", watFile]);
    const actual = instructions(fs.readFileSync(watFile, "utf8"), entry);
    const unary = entry === "sqrtBits", local = unary ? 1 : 2;
    const body = unary ? ["local.get 0", "f64.reinterpret_i64", "f64.sqrt"] :
      ["local.get 0", "f64.reinterpret_i64", "local.get 1", "f64.reinterpret_i64",
        entry === "subBits" ? "f64.sub" : "f64.div"];
    if (entry === "sqrtDivBits") body.push("i64.reinterpret_f64", "f64.reinterpret_i64", "f64.sqrt");
    assert.deepEqual(actual, [...body, "i64.reinterpret_f64", `local.set ${local}`, `local.get ${local}`]);
    const ir = run([compiler, "dump-ir", ...args]);
    for (const op of entry === "sqrtDivBits" ? ["Div", "Sqrt"] :
      [entry === "sqrtBits" ? "Sqrt" : entry === "subBits" ? "Sub" : "Div"])
      assert.equal(ir.split(`f64${op}Bits`).length - 1, 1, `${entry} IR ${op}`);
    const report = run([compiler, "report", ...args]);
    assert.ok(report.includes("compiler-recognized UInt64 bit-pattern floating-point intrinsic"));
    assert.equal(report.includes("Float.ofBits"), false);
    const bytes = fs.readFileSync(wasm);
    if (entry !== "sqrtDivBits") {
      const opcode = entry === "subBits" ? 161 : entry === "divBits" ? 163 : 159;
      const seq = Buffer.from(unary ? [32,0,191,opcode,189,33,1,32,1,11] :
        [32,0,191,32,1,191,opcode,189,33,2,32,2,11]);
      assert.ok(bytes.includes(seq), `${entry}: exact binary opcode sequence missing`);
    }
    for (const [inputs, expected] of vectors[entry]) {
      const [result] = callI64Slots(wasm, entry, 1, inputs);
      if (expected === "nan") assert.ok(isNaNBits(result), `${entry}: expected NaN class`);
      else assert.equal(result, expected, `${entry}: ${inputs.map(x=>x.toString(16)).join(",")}`);
    }
  }
  console.log("checked sub/div/sqrt lowering, exact WAT/binary sequences, nested unary traversal, signed zero, adjacent values, subnormals, ties, infinities, and NaNs");
}
try { main(); } catch (e) { console.error(e.stack); process.exitCode = 1; }
