#!/usr/bin/env node
"use strict";

const {
  formatError,
  loadRegistry,
  prepareCases,
  selectCase,
} = require("./talos-lib.js");

function usage() {
  console.error("usage: talos-artifact.js prepare <case | --all>");
  process.exit(2);
}

function main() {
  if (process.argv.length !== 4 || process.argv[2] !== "prepare") usage();
  const cases = loadRegistry();
  const selected = process.argv[3] === "--all"
    ? cases
    : [selectCase(cases, process.argv[3])];
  prepareCases(selected);
  console.log(`Talos artifact generation passed: ${selected.length} case(s)`);
}

try {
  main();
} catch (error) {
  console.error(`talos-artifact.js: ${formatError(error)}`);
  process.exit(1);
}
