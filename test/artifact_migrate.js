#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const {
  applyOutputs,
  binaryOutput,
  buildDumpRaw,
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

  let rejectedFrozenChange = false;
  try {
    applyOutputs([binaryOutput(frozen, Buffer.from([1, 2, 3]))]);
  } catch (error) {
    if (!error.message.includes("frozen file differs")) throw error;
    if (!fs.readFileSync(frozen).equals(Buffer.from([0, 97, 115, 109]))) {
      throw new Error("a rejected migration changed a frozen artifact");
    }
    rejectedFrozenChange = true;
  }
  if (!rejectedFrozenChange) {
    throw new Error("migration replaced an existing frozen artifact");
  }

  const repoRoot = path.resolve(__dirname, "..");
  const proofRoot = path.join(repoRoot, "proofs", "talos", "lean");
  let buildCalls = 0;
  buildDumpRaw((command, args, options) => {
    buildCalls += 1;
    const expectedArgs = [
      "--timeout", "15m",
      "lake", "-d", proofRoot, "build", "Project.Artifact.Binary.DumpRaw",
    ];
    if (command !== path.join(repoRoot, "tools", "leanrun") ||
        JSON.stringify(args) !== JSON.stringify(expectedArgs) ||
        options.cwd !== repoRoot || options.env !== process.env ||
        options.stdio !== "inherit") {
      throw new Error("raw-module decoder build used the wrong local command envelope");
    }
    return { status: 0, signal: null };
  });
  if (buildCalls !== 1) throw new Error("raw-module decoder target was not built exactly once");

  try {
    buildDumpRaw(() => ({ status: 7, signal: null }));
    throw new Error("raw-module decoder accepted a failed build");
  } catch (error) {
    if (!error.message.includes("exit status 7")) throw error;
  }
  try {
    buildDumpRaw(() => ({ status: null, signal: "SIGTERM" }));
    throw new Error("raw-module decoder accepted a signaled build");
  } catch (error) {
    if (!error.message.includes("terminated by SIGTERM")) throw error;
  }
  try {
    buildDumpRaw(() => ({ error: new Error("spawn failed"), status: null, signal: null }));
    throw new Error("raw-module decoder accepted a spawn failure");
  } catch (error) {
    if (!error.message.includes("raw-module decoder build failed: spawn failed")) throw error;
  }

  process.stdout.write(
    "checked transactional artifact migration, frozen-file identity, and cold-cache decoder build\n",
  );
} finally {
  fs.rmSync(root, { recursive: true, force: true });
}
