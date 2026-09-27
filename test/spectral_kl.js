#!/usr/bin/env node
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const { runChecked } = require('../tools/run-process');
const host = require('./wasmtime_host');

const moduleName = 'LeanExe.Examples.SpectralKL';
const outDir = path.join('.lake', 'build', 'spectral-kl');
const wasm = path.join(outDir, 'spectral-kl.wasm');
const entries = ['equalMoments'];

function bits(value) {
  const b = Buffer.alloc(8);
  b.writeDoubleLE(value);
  return b.readBigUInt64LE();
}
function number(word) {
  const b = Buffer.alloc(8);
  b.writeBigUInt64LE(word);
  return b.readDoubleLE();
}
function call(entry, words) {
  const result = host.call(wasm, entry, 'slots:2', words.map(host.i64))
    .split(/\s+/).map(x => BigInt.asUintN(64, BigInt(x)));
  assert.equal(result.length, 2);
  return { status: result[0], bits: result[1], value: number(result[1]) };
}
function build() {
  fs.mkdirSync(outDir, { recursive: true });
  runChecked(['lake', 'build', moduleName], { encoding: 'utf8', timeout: 120000 });
  runChecked([process.env.LEAN_WASM_EXE || '.lake/build/bin/lean-wasm', 'compile',
    '--module', moduleName, '--entries', entries.map(e => `${moduleName}.${e}`).join(','),
    '--out', wasm], { encoding: 'utf8', timeout: 120000 });
}
function main() {
  build();
  for (const d of [0, -0, 1, -1, 0.5, -0.25, 1e-8, 1e-160, Number.MIN_VALUE]) {
    const result = call('equalMoments', [bits(d)]);
    assert.equal(result.status, 0n);
    assert.equal(result.bits, bits(0.5 * (d*d)));
    assert.ok(Math.abs(result.value - d*d/2) <= 2*Number.EPSILON);
  }
  for (const d of [1.0000000000000002, -1.0000000000000002, Infinity, -Infinity, NaN]) {
    const result = call('equalMoments', [bits(d)]);
    assert.equal(result.status, 1n);
    assert.equal(result.bits, 0n);
  }
  console.log('spectral KL iteration 1: compiled WASM, 9 accepted and 5 rejected cases passed');
}
if (require.main === module) main();
module.exports = { bits, number, call, build, wasm };
