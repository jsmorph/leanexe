#!/usr/bin/env node
"use strict";
const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const { sectionMetadata } = require("../tools/byte-io-kernel");
const { auditAxioms, embeddedSource, byteLookupSource } = require("../tools/byte-io-proof");
const names = ["Example.prefix", "Example.success"];
const valid = "'Example.prefix' depends on axioms: [propext, Quot.sound]\n'Example.success' does not depend on any axioms\n";
auditAxioms(valid, names);
for (const axiom of ["sorryAx", "Lean.ofReduceBool", "Example._native.native_decide.ax_1", "Unknown.axiom"]) {
  assert.throws(() => auditAxioms(valid.replace("propext", axiom), names), /unsupported axiom/);
}
assert.throws(() => auditAxioms(valid.split("\n")[0], names), /missing or extra/);
assert.throws(() => auditAxioms(valid.replace("Example.success", "Example.prefix"), names), /theorem audit/);
assert.throws(() => auditAxioms(valid + valid, names), /missing or extra/);
const bytes = Buffer.from([0, 255, 13, 10]);
assert.match(embeddedSource(bytes), /0, 255, 13, 10/);
assert.notEqual(embeddedSource(bytes), embeddedSource(Buffer.from([0, 254, 13, 10])));
const fixture = fs.readFileSync(path.join(__dirname, "../proofs/byte-io/echo.wasm"));
const moduleRoot = path.join(__dirname, "../proofs/talos/lean/Project/ByteIO");
assert.equal(embeddedSource(fixture), fs.readFileSync(path.join(moduleRoot, "ArtifactBytes.lean"), "utf8"));
assert.equal(byteLookupSource(fixture), fs.readFileSync(path.join(moduleRoot, "ArtifactByteLookup.lean"), "utf8"));
const sections = sectionMetadata(fixture);
assert.deepEqual(sections.map(s => s.id), [1, 2, 3, 5, 6, 7, 10]);
assert.equal(sections[1].entries.length, 6);
assert.equal(sections.at(-1).entries.at(-1).end, fixture.length);
assert.throws(() => sectionMetadata(fixture.subarray(0, fixture.length - 1)), /section exceeds input/);
console.log("Byte-I/O proof gate: 16 positive and negative checks passed");
