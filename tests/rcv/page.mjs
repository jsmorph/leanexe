// Runs the recount page's calling code, tests/web/rcv/tabulate.js, under Node on canonical files
// and compares each report with the reference's.
//
//   node tests/rcv/page.mjs [--count oakland|maine] [--module PATH] [--bounds FILE] DIR ...
//
// `--count` chooses the module that the page calls, the Oakland module by default.  For each file
// NAME.rcv in each DIR, the script calls `tabulate` of tabulate.js, which calls the export
// `tabulate` of a fresh instance of the module, and requires the report to equal NAME.report.  For
// the Oakland module, `edges.py`, `reader_edges.py`, and `check.py` write NAME.report with
// `report` of `tests/rcv/reference.py`, and for the Maine module, `maine/edges.py` and
// `maine/check.py` write it with the reference's Maine mode.  The bound of each call is `boundOf`
// of tabulate.js with the module's constant, the page's bound.  FILE holds the lines of
// `rcv-bound` or `rcv-maine-bound`: a file's path, its size, and its `compiled.tabulate.bound` as
// native Lean evaluates it.  With it, the script requires `boundOf`, when it is not null, to be
// at least that bound, and it calls with that bound when `boundOf` is null.  A file without a
// bound is refused, as the page refuses it.  The script prints each disagreement and refusal and,
// for each directory, the number of files, of well-formed files, whose report is a count's, of
// malformed files, whose report is an error report, and the largest bound of a call.  The exit
// status is 1 when a report differs, a file is refused, or a bound is missing, stale, or below the
// native one, and 2 when a path or the module's name is unknown.  The default module is
// build/verified/rcvTabulate.wasm or build/verified/rcvMaine.wasm.

import { existsSync, readdirSync, readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { boundOf, load, MODULES, Refusal, tabulate } from "../web/rcv/tabulate.js";

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "../..");
const args = process.argv.slice(2);
let count = "oakland";
let modulePath = null;
let boundsPath = null;
const dirs = [];
for (let i = 0; i < args.length; i++) {
  if (args[i] === "--count") count = args[++i];
  else if (args[i] === "--module") modulePath = args[++i];
  else if (args[i] === "--bounds") boundsPath = args[++i];
  else dirs.push(args[i]);
}
if (dirs.length === 0 || !Object.hasOwn(MODULES, count)) {
  console.error("usage: node tests/rcv/page.mjs [--count oakland|maine] [--module PATH] " +
                "[--bounds FILE] DIR ...");
  process.exit(2);
}
const { constant } = MODULES[count];
modulePath ??= path.join(root, "build/verified", MODULES[count].file);
for (const p of [modulePath, boundsPath, ...dirs]) {
  if (p !== null && !existsSync(p)) {
    console.error(`page.mjs: ${p} does not exist`);
    process.exit(2);
  }
}

const native = new Map();
if (boundsPath !== null) {
  for (const line of readFileSync(boundsPath, "utf8").split("\n")) {
    if (line === "") continue;
    const [file, size, bound] = line.split(" ");
    native.set(path.resolve(file), { size: Number(size), bound: BigInt(bound) });
  }
}

/** The bound of the call on `file`, or a reason to refuse it. */
function boundFor(file, bytes) {
  const page = boundOf(bytes.length, constant);
  const exact = native.get(path.resolve(file));
  if (exact !== undefined && exact.size !== bytes.length) {
    return { refusal: `the native bound is of a file of ${exact.size} bytes` };
  }
  if (page !== null && exact !== undefined && page < exact.bound) {
    return { refusal: `boundOf gives ${page}, below the native bound ${exact.bound}` };
  }
  const bound = page ?? exact?.bound;
  return bound === undefined ? { refusal: "no bound" } : { bound };
}

const { sha256, module } = await load(readFileSync(modulePath));
console.log(`${path.relative(process.cwd(), modulePath)}: SHA-256 ${sha256}`);
let failed = 0;
for (const dir of dirs) {
  const names = readdirSync(dir).filter(name => name.endsWith(".rcv")).sort();
  let errors = 0;
  let counts = 0;
  let largest = 0n;
  for (const name of names) {
    const file = path.join(dir, name);
    const bytes = new Uint8Array(readFileSync(file));
    const { bound, refusal } = boundFor(file, bytes);
    let report;
    try {
      if (refusal !== undefined) throw new Refusal(refusal);
      report = await tabulate(module, bytes, bound);
    } catch (e) {
      if (!(e instanceof Refusal)) throw e;
      console.log(`${file}: refused: ${e.message}`);
      failed++;
      continue;
    }
    if (bound > largest) largest = bound;
    if (!readFileSync(file.replace(/\.rcv$/, ".report")).equals(report)) {
      console.log(`${file}: the report differs from the reference's`);
      failed++;
    }
    if (new TextDecoder().decode(report).split("\n")[2].startsWith("error ")) errors++;
    else counts++;
  }
  console.log(`${dir}: ${names.length} files, ${counts} well-formed, ${errors} malformed, ` +
              `largest bound ${largest} bytes`);
}
console.log(`${failed} files refused or with a disagreement`);
process.exit(failed === 0 ? 0 : 1);
