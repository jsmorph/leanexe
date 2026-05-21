#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const roots = ["test", "tools"];
const blocked = [`${["Web", "Assembly"].join("")}.`, `${["Web", "Assembly"].join("")}`];
const self = path.normalize(path.join("test", "no_js_wasm_execution.js"));

function walk(dir, out) {
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      walk(full, out);
    } else if (entry.isFile() && full.endsWith(".js")) {
      out.push(path.normalize(full));
    }
  }
}

function main() {
  const files = [];
  roots.forEach((root) => walk(root, files));
  const offenders = [];
  for (const file of files) {
    if (file === self) {
      continue;
    }
    const text = fs.readFileSync(file, "utf8");
    if (blocked.some((pattern) => text.includes(pattern))) {
      offenders.push(file);
    }
  }
  if (offenders.length !== 0) {
    throw new Error(`JavaScript WASM execution reference found in ${offenders.join(", ")}`);
  }
  process.stdout.write("checked JavaScript WASM execution guard\n");
}

try {
  main();
} catch (error) {
  process.stderr.write(`${error.message}\n`);
  process.exit(1);
}
