"use strict";

const assert = require("node:assert/strict");
const { decodeOutput, decodeCertificates } = require("../tools/euler-riemann-complete");

const n = 2;
const bytes = Buffer.alloc(8 * (4 + 2 * n * n + 12));
bytes.writeDoubleLE(0.8, 8);
bytes.writeBigUInt64LE(2n, 16);
bytes.writeBigUInt64LE(2n, 24);
for (let i = 0; i < 8; i++) bytes.writeDoubleLE(1, 8 * (4 + i));
for (let i = 0; i < 4; i++) {
  const offset = 8 * (12 + 3 * i);
  bytes.writeDoubleLE(-(2 ** (-40 - i)), offset + 8);
  bytes.writeDoubleLE(2 ** (-42 - i), offset + 16);
}
const words = Array.from({ length: bytes.length / 8 }, (_, i) => bytes.readBigUInt64LE(8 * i));
assert.deepEqual(decodeOutput(`[${words.join(",")}]`, n, true), bytes);
assert.throws(() => decodeOutput(`[${words.join(",")}]`, n), /wrong output length/);
assert.throws(() => decodeOutput(`[${words.slice(0, -1).join(",")}]`, n, true), /wrong output length/);

const certificates = decodeCertificates(bytes, n);
assert.deepEqual(certificates.map(x => x.component), ["mass", "xMomentum", "yMomentum", "energy"]);
for (let i = 0; i < 4; i++) {
  assert.equal(certificates[i].absoluteBound, 2 ** (-40 - i));
  assert.equal(certificates[i].lowerBits, words[13 + 3 * i].toString());
  assert.equal(certificates[i].upperBits, words[14 + 3 * i].toString());
}

for (const mutate of [
  b => b.writeBigUInt64LE(1n, 96),
  b => b.writeDoubleLE(NaN, 104),
  b => b.writeDoubleLE(Infinity, 112),
  b => b.writeDoubleLE(1, 104),
]) {
  const invalid = Buffer.from(bytes);
  mutate(invalid);
  assert.throws(() => decodeCertificates(invalid, n), /certificate.*raw output retained/);
}

console.log("Euler certificate output tests passed");
