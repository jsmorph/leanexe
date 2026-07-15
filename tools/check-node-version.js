#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const versionFile = path.join(__dirname, "..", ".node-version");
const expected = `v${fs.readFileSync(versionFile, "utf8").trim()}`;

if (process.version !== expected) {
  process.stderr.write(`Node.js version mismatch: expected ${expected}, got ${process.version}.\n`);
  process.exit(1);
}

console.log(`checked Node.js ${expected}`);
