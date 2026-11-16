// Runs the conjunction page's calling code, tests/web/conjunction/assess.js, under Node on the
// module cases of `assess` and compares each result with native Lean's.
//
//   node tests/conjunction/page.mjs [--module PATH] CASES
//
// CASES holds the lines that `verified-cases-conjunction` prints,
// `module|export|kind|args|expected`.
// For each line of the export `assess`, the script calls `assess` of assess.js, which calls the
// export on a fresh instance of the module with the arguments as the page passes them, numbers for
// the floats and a BigInt for the panel count, and requires the status, the bits of `lo` and `hi`,
// and the verdict to equal the expected words.  It prints each disagreement and the number of
// calls, and its exit status is 1 when a result differs and 2 when a path is missing.  The default
// module is build/verified/conjunction.wasm.

import { existsSync, readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { assess, load } from "../web/conjunction/assess.js";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..");
const args = process.argv.slice(2);
let modulePath = path.join(root, "build/verified/conjunction.wasm");
if (args[0] === "--module") {
  modulePath = args[1];
  args.splice(0, 2);
}
if (args.length !== 1) {
  console.error("usage: node tests/conjunction/page.mjs [--module PATH] CASES");
  process.exit(2);
}
for (const p of [modulePath, args[0]]) {
  if (!existsSync(p)) {
    console.error(`page.mjs: ${p} does not exist`);
    process.exit(2);
  }
}

const view = new DataView(new ArrayBuffer(8));
const fromBits = b => (view.setBigUint64(0, BigInt(b)), view.getFloat64(0));
const toBits = x => (view.setFloat64(0, x), view.getBigUint64(0));

const { module, sha256 } = await load(readFileSync(modulePath));
let calls = 0;
let failures = 0;
for (const line of readFileSync(args[0], "utf8").split("\n")) {
  const [name, entry, , argText, expected] = line.split("|");
  if (name !== "conjunction" || entry !== "assess") continue;
  const words = argText.split(" ").map(w => w.split(":"));
  const [m1, m2, c11, c12, c22, r, t] = words.slice(0, 7).map(([, b]) => fromBits(b));
  const n = BigInt(words[7][1]);
  const got = await assess(module, { m1, m2, c11, c12, c22, r, t, n });
  const text = `${got.status} ${toBits(got.lo)} ${toBits(got.hi)} ${got.verdict}`;
  calls++;
  if (text !== expected) {
    failures++;
    console.log(`differs: ${argText}: expected ${expected}, got ${text}`);
  }
}
console.log(`${modulePath} ${sha256}: ${calls} calls of assess, ${failures} differ`);
process.exit(failures || calls === 0 ? 1 : 0);
