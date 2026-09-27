#!/usr/bin/env node
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const { runChecked } = require('../tools/run-process');
const host = require('./wasmtime_host');

const moduleName = 'LeanExe.Examples.SpectralKL';
const outDir = path.join('.lake', 'build', 'spectral-kl');
const wasm = path.join(outDir, 'spectral-kl.wasm');
const entries = ['equalMoments', 'kernel2', 'kernel40', 'scalarMoments', 'fromSamples', 'fromUnitSamples', 'fromBoundedSamples'];

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
  // Independent composite Simpson quadrature of the defining integral.
  function integral(delta) {
    const n = 4096;
    let sum = 1;
    for (let i = 1; i < n; i++) {
      const r = i/n;
      sum += (i%2 ? 4 : 2)*(1-r)/(1+r*delta);
    }
    return sum/(3*n);
  }
  let maxError = 0;
  for (const d of [-0.5, -0.25, -1e-8, -1e-16, -0, 0, 1e-16, 1e-8, 0.25, 0.5]) {
    const result = call('kernel2', [bits(d)]);
    assert.equal(result.status, 0n);
    const error = Math.abs(result.value - integral(d));
    maxError = Math.max(error, maxError);
    assert.ok(error <= Math.abs(d)**3/10 + 71*Number.EPSILON + 2e-14,
      `kernel2(${d}) error ${error}`);
  }
  for (const d of [0.5000000000000001, -0.5000000000000001, Infinity, NaN]) {
    assert.equal(call('kernel2', [bits(d)]).status, 1n);
  }
  console.log(`spectral KL iteration 2: 10 quadrature comparisons and 4 rejections passed; max error ${maxError}`);
  const deltas = [-0.5, 0.5, -0, 0, -1e-16, 1e-16, -1e-8, 1e-8];
  for (let i=0; i<=100; i++) deltas.push(i/100-0.5);
  const oracle = JSON.parse(runChecked(['python3', 'test/spectral_kl_oracle.py'], {
    input: JSON.stringify(deltas), encoding: 'utf8',
  }).stdout);
  maxError = 0;
  for (let i=0; i<deltas.length; i++) {
    const result = call('kernel40', [bits(deltas[i])]);
    assert.equal(result.status, 0n);
    const error = Math.abs(result.value - Number(oracle[i]));
    maxError = Math.max(maxError, error);
    assert.ok(error <= 1e-14, `kernel40(${deltas[i]}) error ${error}`);
  }
  for (const [p,q,eta] of [
    [[0.25,0.5,0.75],[-0.25,0,0.25],1], [[-1,1],[-1,1],1],
    [[1],[0.9],2], [[-0,0],[0,-0],0.25],
  ]) {
    const mean = a => a.reduce((s,x)=>s+x,0)/a.length;
    const second = a => a.reduce((s,x)=>s+x*x,0)/a.length;
    const a = second(p)+eta, b = second(q)+eta, d = mean(p)-mean(q);
    const expected = d*d/b*integral(a/b-1);
    const result = host.call(wasm, 'fromSamples', 'slots:2',
      [host.arrayU64(p.map(bits)), host.arrayU64(q.map(bits)), host.i64(bits(eta))])
      .split(/\s+/).map(x=>BigInt.asUintN(64,BigInt(x)));
    assert.equal(result[0],0n);
    assert.ok(Math.abs(number(result[1])-expected) < 1e-13);
  }
  for (const [p,q,eta,status] of [
    [[],[1],1,1n], [[NaN],[1],1,1n], [[17],[1],1,1n],
    [[0],[0],0,1n], [[1],[0],0.25,2n],
  ]) {
    const result = host.call(wasm,'fromSamples','slots:2',
      [host.arrayU64(p.map(bits)),host.arrayU64(q.map(bits)),host.i64(bits(eta))])
      .split(/\s+/).map(x=>BigInt.asUintN(64,BigInt(x)));
    assert.deepEqual(result,[status,0n]);
  }
  console.log(`spectral KL iteration 3: ${deltas.length} high-precision kernel checks; max error ${maxError}; sample-to-score and rejection checks passed`);
  // Exercise the entry whose complete source error theorem is
  // Scalar.fromUnitSamples_correct. These calls check compiler/ABI integration.
  for(const [p,q] of [
    [[0.5],[-0.5]], [[0.1,0.3,-0.2],[0.2,0.4]], [[0,-0],[0]],
  ]) {
    const words=host.call(wasm,'fromUnitSamples','slots:2',
      [host.arrayU64(p.map(bits)),host.arrayU64(q.map(bits))])
      .split(/\s+/).map(x=>BigInt.asUintN(64,BigInt(x)));
    assert.equal(words[0],0n);
    assert.ok(Number.isFinite(number(words[1])));
  }
  for(const eta of [1,3.5,256]) {
    const words=host.call(wasm,'fromBoundedSamples','slots:2',
      [host.arrayU64([0.5].map(bits)),host.arrayU64([-0.5].map(bits)),host.i64(bits(eta))])
      .split(/\s+/).map(x=>BigInt.asUintN(64,BigInt(x)));
    assert.equal(words[0],0n);
    assert.ok(Number.isFinite(number(words[1])));
  }
  console.log('Complete scalar estimator: WASM entry and ABI integration passed');
}
if (require.main === module) main();
module.exports = { bits, number, call, build, wasm };
