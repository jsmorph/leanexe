#!/usr/bin/env node
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const { installProgramCache } = require("../tools/talos-lib");
const { makeTemporaryDirectory } = require("../tools/temp-directory");

const root = makeTemporaryDirectory("leanexe-talos-cache-");
const item = { name: "example", leanModule: "Example" };
const destination = path.join(root, "Project", "Example", "Program.lean");
const generated = path.join(root, "generated.lean");

try {
  fs.mkdirSync(path.dirname(destination), { recursive: true });
  fs.writeFileSync(destination, "def value := 1\n");
  fs.writeFileSync(generated, "def value := 1\n");
  installProgramCache(item, generated, "check", root);

  fs.writeFileSync(generated, "def value := 2\n");
  let rejected = false;
  try {
    installProgramCache(item, generated, "check", root);
  } catch (error) {
    if (!error.message.includes("differs from the tracked cache")) throw error;
    rejected = true;
  }
  if (!rejected) throw new Error("Talos cache check accepted different generated content");
  if (fs.readFileSync(destination, "utf8") !== "def value := 1\n") {
    throw new Error("Talos cache check changed the tracked cache");
  }
  installProgramCache(item, generated, "refresh", root);
  if (fs.readFileSync(destination, "utf8") !== "def value := 2\n") {
    throw new Error("Talos cache refresh did not install the generated cache");
  }
} finally {
  fs.rmSync(root, { recursive: true, force: true });
}

process.stdout.write("checked nonmutating Talos cache comparison and explicit refresh\n");
