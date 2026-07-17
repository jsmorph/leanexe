#!/usr/bin/env node
"use strict";

const {
  checkAllProofs,
  checkCase,
  formatError,
  loadRegistry,
  prepareCases,
  selectCase,
} = require("./talos-lib.js");

function usage() {
  console.error("usage: talos-proof.js check <case | --all>");
  process.exit(2);
}

function main() {
  if (process.argv.length !== 4 || process.argv[2] !== "check") usage();
  const cases = loadRegistry();
  if (process.argv[3] === "--all") {
    prepareCases(cases);
    checkAllProofs(cases);
    const count = cases.filter((item) => item.complete).length;
    console.log(`Talos proof library passed: ${count} completed case(s)`);
    return;
  }

  const selected = selectCase(cases, process.argv[3]);
  prepareCases([selected]);
  checkCase(selected);
  if (selected.complete) {
    console.log(`Talos proof passed: ${selected.name}`);
  } else {
    console.log(`Talos incomplete case target built: ${selected.name}`);
  }
}

try {
  main();
} catch (error) {
  console.error(`talos-proof.js: ${formatError(error)}`);
  process.exit(1);
}
