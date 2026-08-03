"use strict";

const crypto = require("node:crypto");
const fs = require("node:fs");
const path = require("node:path");

const verifierRelativeRoot = path.join(
  "proofs", "talos", "lean", "Project", "Artifact", "Binary",
);
const verifierRelativeSources = [
  "Syntax.lean",
  "Cursor.lean",
  "Leb.lean",
  "Primitives.lean",
  "Decode.lean",
  "Grammar.lean",
  "Validity.lean",
  "Validate.lean",
  "Translate.lean",
  "Equality.lean",
  "Evidence.lean",
  "Proof/Cursor.lean",
  "Proof/Leb.lean",
  "Proof/Primitives.lean",
  "Proof/Decode.lean",
  "Proof/Validate.lean",
  "Proof/Translate.lean",
];

function compareText(left, right) {
  if (left < right) return -1;
  if (left > right) return 1;
  return 0;
}

function collectLeanSources(root, relative = "") {
  const directory = path.join(root, relative);
  const sources = [];
  for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
    const child = path.join(relative, entry.name);
    if (entry.isDirectory()) {
      sources.push(...collectLeanSources(root, child));
    } else if (entry.isFile() && entry.name.endsWith(".lean")) {
      sources.push(child);
    } else if (entry.isSymbolicLink()) {
      throw new Error(`verifier source tree contains a symbolic link: ${child}`);
    }
  }
  return sources.sort(compareText);
}

function leanSourcesUnder(repoRoot, relativeRoots) {
  const sources = [];
  for (const relativeRoot of relativeRoots) {
    const root = path.join(repoRoot, relativeRoot);
    for (const relative of collectLeanSources(root)) {
      sources.push({
        absolute: path.join(root, relative),
        relative: path.join(relativeRoot, relative).split(path.sep).join("/"),
      });
    }
  }
  return sources.sort((left, right) => compareText(left.relative, right.relative));
}

function verifierSources(repoRoot) {
  return [...verifierRelativeSources].sort(compareText).map((relative) => {
    const absolute = path.join(repoRoot, verifierRelativeRoot, relative);
    const stat = fs.lstatSync(absolute);
    if (!stat.isFile() || stat.isSymbolicLink()) {
      throw new Error(`invalid verifier source: ${relative}`);
    }
    return {
      absolute,
      relative: path.join(verifierRelativeRoot, relative).split(path.sep).join("/"),
    };
  });
}

function verifierSourceSha256(repoRoot) {
  const hash = crypto.createHash("sha256");
  hash.update("leanexe-verifier-source-v1\0");
  for (const source of verifierSources(repoRoot)) {
    const contents = fs.readFileSync(source.absolute);
    hash.update(`${source.relative}\0${contents.length}\0`);
    hash.update(contents);
  }
  return hash.digest("hex");
}

module.exports = {
  leanSourcesUnder,
  verifierRelativeSources,
  verifierSources,
  verifierSourceSha256,
};
