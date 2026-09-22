#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const path = require("node:path");
const { runChecked, spawnResult } = require("../tools/run-process");

const options = {
  cwd: path.resolve(__dirname, ".."),
  encoding: "utf8",
  timeout: 300000,
};

function main() {
  const command = ["tools/trace-policy"];
  const all = runChecked(command, options);
  process.stdout.write(all.stdout);
  assert.match(all.stdout, /Checked 46 synthetic traces and transition invariants\./);

  const selected = runChecked([...command, "budget-exceeded"], options);
  assert.match(selected.stdout, /5: before write fd=3 count=1/);
  assert.match(selected.stdout, /STOP at event 5/);

  const missing = spawnResult([...command, "no-such-sample"], options);
  assert.equal(missing.status, 2);
  assert.match(missing.stderr, /unknown sample: no-such-sample/);
  console.log("Checked sample selection and unknown-sample exit status.");
}

try { main(); }
catch (error) { console.error(error.stack); process.exitCode = 1; }
