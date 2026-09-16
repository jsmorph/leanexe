#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { runPrng } = require("../tools/prng");
const { runChecked, spawnResult } = require("../tools/run-process");

const root = path.resolve(__dirname, "..");
const reference = path.join(root, "build/prng/reference");
const options = { cwd: root, encoding: "utf8", timeout: 120000 };

function lines(output) {
  return output.trim() === "" ? [] : output.trim().split("\n");
}

function main() {
  fs.mkdirSync(path.dirname(reference), { recursive: true });
  runChecked(["cc", "-std=c11", "-Wall", "-Wextra", "-Werror", "-O2",
    "test/prng_reference.c", "-o", reference], options);
  const cases = [
    ["0", "0", "10"],
    ["0", "5", "18446744073709551615"],
    ["1", "16", "1"],
    ["42", "32", "100"],
    ["18446744073709551615", "32", "4294967296"],
    ["18446744073709551615", "32", "18446744073709551615"],
    ["11400714819323198485", "257", "257"],
  ];
  for (const args of cases) {
    const actual = runPrng(...args);
    assert.equal(actual.length, Number(args[1]));
    assert.deepEqual(actual, lines(runChecked([reference, ...args], options).stdout));
    assert.deepEqual(actual, lines(runChecked(["lake", "env", "lean", "--run",
      "test/PrngNative.lean", ...args], options).stdout));
  }
  assert.deepEqual(runPrng("0", "5", "18446744073709551615"), [
    "16294208416658607535", "7960286522194355700", "487617019471545679",
    "17909611376780542444", "1961750202426094747",
  ]);
  assert.deepEqual(runPrng("42", "32", "100"), runPrng("42", "32", "100"));
  const cli = [process.execPath, "tools/prng.js"];
  assert.deepEqual(lines(runChecked([...cli, "42", "5", "100"], options).stdout),
    runPrng("42", "5", "100"));
  assert.equal(runChecked([...cli, "0", "0", "1"], options).stdout, "");
  const failingHost = path.join(root, "build/prng/failing-host.sh");
  fs.writeFileSync(failingHost, "#!/bin/sh\nprintf '%s\\n' 'PRNG host failure' >&2\nexit 7\n", { mode: 0o700 });
  const failure = spawnResult([...cli, "1", "1", "10"], {
    ...options, env: { ...process.env, LEANEXE_WASMTIME_HOST: failingHost },
  });
  assert.equal(failure.status, 7);
  assert.equal(failure.stdout, "");
  assert.match(failure.stderr, /PRNG host failure/);
  for (const args of [[], ["1", "2"], ["1", "2", "0"], ["-1", "2", "3"],
    ["1", "2.5", "3"], ["1", "2", "18446744073709551616"],
    ["18446744073709551616", "2", "3"], ["1", "18446744073709551616", "3"]]) {
    const result = spawnResult([...cli, ...args], options);
    assert.equal(result.status, 2);
    assert.equal(result.stdout, "");
    assert.match(result.stderr, /^prng: /);
  }
  console.log("Checked seven PRNG vectors against C and native Lean, repeatability, counts, modulus boundaries, CLI validation, and failure propagation");
}

try { main(); }
catch (error) { console.error(error.stack); process.exitCode = 1; }
