#!/usr/bin/env node
"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");

function fail(message) {
  throw new Error(message);
}

function digest(bytes) {
  return crypto.createHash("sha256").update(bytes).digest("hex");
}

function main() {
  if (process.argv.length !== 5 || process.argv[2] !== "freeze") {
    fail("usage: artifact-package.js freeze <manifest.json> <program.wasm>");
  }
  const manifestPath = path.resolve(process.argv[3]);
  const inputPath = path.resolve(process.argv[4]);
  const manifest = JSON.parse(fs.readFileSync(manifestPath, "utf8"));
  const bytes = fs.readFileSync(inputPath);
  const foundDigest = digest(bytes);
  if (foundDigest !== manifest.sha256) {
    fail(`SHA-256 mismatch: manifest=${manifest.sha256}, input=${foundDigest}`);
  }
  if (bytes.length !== manifest.byteLength) {
    fail(`byte-length mismatch: manifest=${manifest.byteLength}, input=${bytes.length}`);
  }
  if (path.basename(path.dirname(manifestPath)) !== manifest.sha256) {
    fail("manifest directory does not equal its SHA-256");
  }
  const outputPath = path.join(path.dirname(manifestPath), "program.wasm");
  if (fs.existsSync(outputPath)) {
    const existing = fs.readFileSync(outputPath);
    if (!existing.equals(bytes)) fail(`frozen artifact differs: ${outputPath}`);
    console.log(`Frozen artifact already matches: ${outputPath}`);
    return;
  }
  fs.copyFileSync(inputPath, outputPath, fs.constants.COPYFILE_EXCL);
  console.log(`Frozen artifact: ${outputPath}`);
}

try {
  main();
} catch (error) {
  console.error(`artifact-package.js: ${error.message}`);
  process.exit(1);
}
