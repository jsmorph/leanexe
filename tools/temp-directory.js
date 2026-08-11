"use strict";

const fs = require("node:fs");
const path = require("node:path");

const root = path.resolve(__dirname, "..", "tmp");

function makeTemporaryDirectory(prefix) {
  if (!/^[A-Za-z0-9_-]+-$/.test(prefix)) {
    throw new Error(`invalid temporary-directory prefix: ${JSON.stringify(prefix)}`);
  }
  fs.mkdirSync(root, { recursive: true });
  return fs.mkdtempSync(path.join(root, prefix));
}

module.exports = { makeTemporaryDirectory, root };
