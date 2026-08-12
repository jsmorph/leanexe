#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");

const repoRoot = path.resolve(__dirname, "..");
const roots = [
  "README.md",
  "DEVELOPING.md",
  "plan.md",
  "docs",
  "plans",
  "demos",
  "benchmarks",
  "ltg",
  "paper",
  "proofs/talos/README.md",
  "proofs/talos/lean/Project/ProofKit/README.md",
];
const excludedNames = new Set([
  "baseline-proof-library.md",
  "baseline-proof-strategies.md",
  "proof-journal.md",
  "proof-library.md",
  "proof-strategies.md",
]);
const obsoleteReferences = [
  "docs/better-wasm-proving.md",
  "docs/compiler-theorem-bridge.md",
  "docs/emitter.md",
  "docs/guarantees.md",
  "docs/opacity-proof-boundaries.md",
  "docs/plan-notes.md",
  "docs/reviews.md",
  "docs/strings.md",
  "docs/summary.md",
  "docs/typeclasses.md",
  "docs/wasm-proofs.md",
  "plans/artifact-proof-composition.md",
  "plans/artifact-verification.md",
  "plans/better-wasm-proving.md",
];

function relative(file) {
  return path.relative(repoRoot, file).split(path.sep).join("/");
}

function include(file) {
  const name = path.basename(file);
  const parts = relative(file).split("/");
  const evidenceCopy = parts[0] === "demos" || parts[0] === "benchmarks";
  return path.extname(file) === ".md" &&
    !name.endsWith("journal.md") &&
    !(evidenceCopy && excludedNames.has(name)) &&
    !parts.some((part) => part.endsWith(".proof"));
}

function collect(entry, files) {
  const full = path.join(repoRoot, entry);
  const status = fs.statSync(full);
  if (status.isFile()) {
    if (include(full)) files.push(full);
    return;
  }
  for (const child of fs.readdirSync(full, { withFileTypes: true })) {
    const childEntry = path.join(entry, child.name);
    if (child.isDirectory()) {
      if (!child.name.endsWith(".proof")) collect(childEntry, files);
    } else if (include(path.join(repoRoot, childEntry))) {
      files.push(path.join(repoRoot, childEntry));
    }
  }
}

function localTarget(raw) {
  let target = raw.trim();
  if (target.startsWith("<") && target.endsWith(">")) {
    target = target.slice(1, -1);
  } else {
    target = target.split(/\s+["']/u, 1)[0];
  }
  if (/^[a-z][a-z0-9+.-]*:/iu.test(target) || target.startsWith("#")) return null;
  target = target.split("#", 1)[0].split("?", 1)[0];
  if (target === "") return null;
  try {
    return decodeURIComponent(target);
  } catch {
    return target;
  }
}

const files = [];
for (const root of roots) collect(root, files);
files.sort();
const failures = [];

for (const file of files) {
  const source = fs.readFileSync(file, "utf8");
  const name = relative(file);
  const linkPattern = /!?\[[^\]\n]*\]\(([^)\n]+)\)/gu;
  for (const match of source.matchAll(linkPattern)) {
    const target = localTarget(match[1]);
    if (target === null) continue;
    if (path.isAbsolute(target)) {
      failures.push(`${name}: absolute local link ${target}`);
      continue;
    }
    const resolved = path.resolve(path.dirname(file), target);
    if (resolved !== repoRoot && !resolved.startsWith(`${repoRoot}${path.sep}`)) {
      failures.push(`${name}: local link escapes the repository ${target}`);
      continue;
    }
    if (!fs.existsSync(resolved)) {
      failures.push(`${name}: missing local link ${target}`);
    }
  }
  for (const obsolete of obsoleteReferences) {
    if (source.includes(obsolete)) failures.push(`${name}: obsolete reference ${obsolete}`);
  }
  const withoutLockPath = source.replaceAll("/tmp/vq-leanrun.<uid>/1", "");
  if (/(^|[\s`"'(])\/tmp\//mu.test(withoutLockPath)) {
    failures.push(`${name}: absolute /tmp workspace path`);
  }
}

if (failures.length > 0) {
  for (const failure of failures) process.stderr.write(`${failure}\n`);
  process.exit(1);
}
process.stdout.write(`Checked ${files.length} maintained Markdown files\n`);
