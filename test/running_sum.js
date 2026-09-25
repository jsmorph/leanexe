#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const { runChecked } = require("../tools/run-process");
const { run } = require("./wasi_io_host");

const source = "LeanExe.Examples.RunningSum";
const wasm = "build/running-sum.wasm";

async function main() {
  runChecked(["lake", "build", "lean-wasm", source], { stdio: "inherit" });
  runChecked(["tools/build-wasi-io-host.sh"]);
  runChecked([process.env.LEAN_WASM_EXE || ".lake/build/bin/lean-wasm",
    "compile-wasi-io", "--module", source, "--entry", `${source}.main`, "--out", wasm]);
  runChecked([process.env.WASM_TOOLS || "wasm-tools", "validate", wasm]);

  const inputs = ["", "0\n-0\n+0000\n", "12\n-5\n20\n", "-10\r\n+3\r\n7",
    "9223372036854775807\n1\n-18446744073709551616\n-1\n",
    `${"9".repeat(5000)}\n1\n-${"1" + "0".repeat(5000)}\n`];
  let seed = 73n;
  const values = [];
  for (let i = 0; i < 1000; i += 1) {
    seed = (seed * 6364136223846793005n + 1442695040888963407n) % (1n << 128n);
    values.push((i % 2 ? -seed : seed).toString());
  }
  inputs.push(`${values.join("\n")}\n`);
  for (const input of inputs) {
    let sum = 0n;
    const lines = input === "" ? [] : input.replace(/\n$/, "").split("\n");
    const expected = lines.map(line => `${sum += BigInt(line)}\n`).join("");
    const actual = await run(wasm, input);
    assert.equal(actual.status, 0);
    assert.equal(actual.output.toString(), expected);
    const native = runChecked(["lake", "env", "lean", "--run", "test/RunningSumNative.lean"],
      { input, encoding: "utf8", timeout: 60000 });
    assert.equal(native.stdout, expected);
  }
  for (const bad of ["\n", "+\n", "-\n", "1x\n", " 1\n", "1 2\n", "1\r2\n", "\xff\n"]) {
    const input = `5\n${bad}9\n`;
    const actual = await run(wasm, input);
    assert.equal(actual.status, 28);
    assert.equal(actual.output.toString(), "5\n");
  }

  let observed = "", beforeNewline = null, stage = 0;
  const interactive = await run(wasm, child => {
    child.stdout.on("data", chunk => {
      observed += chunk.toString();
      if (stage === 0 && observed === "12\n") {
        stage = 1;
        child.stdin.write("-5\n");
      } else if (stage === 1 && observed === "12\n7\n") {
        stage = 2;
        child.stdin.end("+20");
      }
    });
    child.stdin.write("12");
    const timer = setTimeout(() => {
      beforeNewline = observed;
      child.stdin.write("\n");
    }, 100);
    child.once("exit", () => clearTimeout(timer));
  });
  assert.equal(beforeNewline, "");
  assert.equal(stage, 2, "each sum must arrive before the next input line is sent");
  assert.equal(interactive.status, 0);
  assert.equal(interactive.output.toString(), "12\n7\n27\n");

  const brokenPipe = await run(wasm, child => {
    child.stdout.destroy();
    child.stdin.end("1\n");
  });
  assert.equal(brokenPipe.status, 64);
  console.log("running sum: arithmetic, native comparison, streaming, EOF, and errors passed");
}

main().catch(error => {
  console.error(error.stack || String(error));
  process.exitCode = 1;
});
