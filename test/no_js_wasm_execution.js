#!/usr/bin/env node

const fs = require("fs");
const path = require("path");

const roots = ["test", "tools"];
const blockedIdentifier = ["Web", "Assembly"].join("");
const self = path.normalize(path.join("test", "no_js_wasm_execution.js"));

function containsBlockedIdentifier(source) {
  let index = 0;

  function skipQuoted(quote) {
    index += 1;
    while (index < source.length) {
      if (source[index] === "\\") {
        index += 2;
      } else if (source[index] === quote) {
        index += 1;
        return;
      } else {
        index += 1;
      }
    }
  }

  function scanTemplate() {
    index += 1;
    while (index < source.length) {
      if (source[index] === "\\") {
        index += 2;
      } else if (source[index] === "`") {
        index += 1;
        return false;
      } else if (source[index] === "$" && source[index + 1] === "{") {
        index += 2;
        if (scanCode(true)) return true;
      } else {
        index += 1;
      }
    }
    return false;
  }

  function scanCode(stopAtBrace) {
    let braces = 0;
    while (index < source.length) {
      const character = source[index];
      if (character === "'" || character === '"') {
        skipQuoted(character);
      } else if (character === "`") {
        if (scanTemplate()) return true;
      } else if (character === "/" && source[index + 1] === "/") {
        index += 2;
        while (index < source.length && source[index] !== "\n") index += 1;
      } else if (character === "/" && source[index + 1] === "*") {
        index += 2;
        while (index + 1 < source.length &&
               !(source[index] === "*" && source[index + 1] === "/")) {
          index += 1;
        }
        index = Math.min(index + 2, source.length);
      } else if (/[A-Za-z_$]/.test(character)) {
        const start = index;
        index += 1;
        while (index < source.length && /[A-Za-z0-9_$]/.test(source[index])) index += 1;
        if (source.slice(start, index) === blockedIdentifier) return true;
      } else if (stopAtBrace && character === "{") {
        braces += 1;
        index += 1;
      } else if (stopAtBrace && character === "}") {
        index += 1;
        if (braces === 0) return false;
        braces -= 1;
      } else {
        index += 1;
      }
    }
    return false;
  }

  return scanCode(false);
}

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
  const probes = [
    ["WebAssembly.instantiate(bytes)", true],
    ["const api = WebAssembly", true],
    ["`result: ${WebAssembly.Module}`", true],
    ["'WebAssembly testsuite'", false],
    ["// WebAssembly.instantiate\nconst value = 1", false],
    ["/* WebAssembly.Module */ const value = 1", false],
    ["`WebAssembly testsuite`", false],
  ];
  for (const [source, expected] of probes) {
    if (containsBlockedIdentifier(source) !== expected) {
      throw new Error(`JavaScript execution guard misclassified ${JSON.stringify(source)}`);
    }
  }

  const files = [];
  roots.forEach((root) => walk(root, files));
  const offenders = [];
  for (const file of files) {
    if (file === self) {
      continue;
    }
    const text = fs.readFileSync(file, "utf8");
    if (containsBlockedIdentifier(text)) {
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
