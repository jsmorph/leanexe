"use strict";

const assert = require("node:assert/strict");
const fs = require("node:fs");
const path = require("node:path");
const test = require("node:test");
const { instantiate } = require("../../tools/wgsl/wasm-host");
const host = fs.readFileSync(path.join(__dirname, "host/host.wasm"));
const metadata = JSON.parse(fs.readFileSync(path.join(__dirname, "packages/scalar/manifest.json"), "utf8"));

test("the checked Wasm body forwards offsets and copies little-endian words", () => {
  const bridge = instantiate(host, metadata, inputs => {
    assert.deepEqual(inputs, { a: [0x3f800000], b: [0x40000000] });
    return { outputs: [0x40000000] };
  });
  const { memory, run } = bridge.instance.exports;
  new Uint8Array(memory.buffer).fill(0xa5);
  const view = new DataView(memory.buffer);
  view.setUint32(16, 0x3f800000, true);
  view.setUint32(40, 0x40000000, true);
  const before = Buffer.from(new Uint8Array(memory.buffer));
  assert.equal(run(16, 40, 64), 0);
  assert.equal(bridge.calls, 1);
  assert.deepEqual([...new Uint8Array(memory.buffer, 64, 4)], [0, 0, 0, 64]);
  const after = Buffer.from(memory.buffer);
  assert.deepEqual(after.subarray(0, 64), before.subarray(0, 64));
  assert.deepEqual(after.subarray(68), before.subarray(68));
});

test("both inputs are snapshotted before an overlapping output is written", () => {
  const bridge = instantiate(host, metadata, inputs => {
    assert.deepEqual(inputs, { a: [0x3f800000], b: [0x3f800000] });
    return { outputs: [0x40400000] };
  });
  const view = new DataView(bridge.instance.exports.memory.buffer);
  view.setUint32(0, 0x3f800000, true);
  assert.equal(bridge.instance.exports.run(0, 0, 0), 0);
  assert.equal(view.getUint32(0, true), 0x40400000);
});

test("misaligned and out-of-bounds regions fail before native dispatch or memory changes", () => {
  const bridge = instantiate(host, metadata, () => { throw new Error("unexpected dispatch"); });
  const { memory, run } = bridge.instance.exports;
  const before = Buffer.from(new Uint8Array(memory.buffer));
  for (const offsets of [[1, 4, 8], [0, 5, 8], [0, 4, 9], [65536, 4, 8], [0, 65536, 8], [0, 4, 65536], [-4, 4, 8]]) {
    assert.throws(() => run(...offsets), /aligned|outside Wasm memory/);
    assert.deepEqual(Buffer.from(memory.buffer), before);
  }
  assert.equal(bridge.calls, 0);
});

test("a failed or malformed native result commits no output bytes", () => {
  for (const response of [{ outputs: [] }, { outputs: [-1] }, { outputs: [2 ** 32] }, { outputs: [1.5] }]) {
    const bridge = instantiate(host, metadata, () => response);
    const { memory, run } = bridge.instance.exports;
    new Uint8Array(memory.buffer).fill(0xa5);
    const before = Buffer.from(new Uint8Array(memory.buffer));
    assert.throws(() => run(0, 4, 8), /invalid native output/);
    assert.deepEqual(Buffer.from(memory.buffer), before);
  }
});
