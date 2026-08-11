#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const {
  applyOutputs,
  binaryOutput,
  textOutput,
} = require("../tools/artifact-migrate");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

const root = makeTemporaryDirectory("leanexe-migrate-test-");
try {
  const existing = path.join(root, "existing.txt");
  const created = path.join(root, "nested", "created.txt");
  const frozen = path.join(root, "program.wasm");
  fs.writeFileSync(existing, "old\n");
  fs.writeFileSync(frozen, Buffer.from([0, 97, 115, 109]));

  applyOutputs([
    textOutput(existing, "new"),
    textOutput(created, "created"),
    binaryOutput(frozen, Buffer.from([0, 97, 115, 109])),
  ]);
  if (fs.readFileSync(existing, "utf8") !== "new\n" ||
      fs.readFileSync(created, "utf8") !== "created\n") {
    throw new Error("transactional migration did not install every prepared output");
  }

  try {
    applyOutputs([binaryOutput(frozen, Buffer.from([1, 2, 3]))]);
  } catch (error) {
    if (!error.message.includes("frozen file differs")) throw error;
    if (!fs.readFileSync(frozen).equals(Buffer.from([0, 97, 115, 109]))) {
      throw new Error("a rejected migration changed a frozen artifact");
    }
    process.stdout.write("checked transactional artifact migration and frozen-file identity\n");
    process.exitCode = 0;
    return;
  }
  throw new Error("migration replaced an existing frozen artifact");
} finally {
  fs.rmSync(root, { recursive: true, force: true });
}
