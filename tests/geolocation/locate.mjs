// Calls the export `locate` of the geolocation module on input arrays and prints each output.
//
//   node tests/geolocation/locate.mjs MODULE [REPEAT] < INPUTS > OUTPUTS
//
// Each input line is a JSON array of the bit patterns of the input values, as 16 hexadecimal
// digits.  Each output line is a JSON object with the bit patterns of the output values and the
// time of the call in milliseconds, the median of REPEAT calls (default 1).  Every call runs in a
// fresh instance of the module, whose allocator `alloc` places the input array: its length in the
// first word and its values after.

import { readFileSync } from "node:fs";
import readline from "node:readline";

const module = await WebAssembly.compile(readFileSync(process.argv[2]));
const repeat = Number(process.argv[3] ?? "1");

/** One call in a fresh instance: the output's bit patterns and the time of the call. */
async function call(bits) {
  const x = (await WebAssembly.instantiate(module)).exports;
  const ptr = x.alloc(BigInt(8 + 8 * bits.length));
  let view = new DataView(x.memory.buffer);
  view.setBigUint64(Number(ptr), BigInt(bits.length), true);
  bits.forEach((b, i) => view.setBigUint64(Number(ptr) + 8 + 8 * i, b, true));
  const start = performance.now();
  const out = Number(x.locate(ptr));
  const ms = performance.now() - start;
  view = new DataView(x.memory.buffer);
  const n = Number(view.getBigUint64(out, true));
  const ys = [];
  for (let i = 0; i < n; i++) {
    ys.push(view.getBigUint64(out + 8 + 8 * i, true).toString(16).padStart(16, "0"));
  }
  return { ys, ms };
}

const lines = readline.createInterface({ input: process.stdin });
for await (const line of lines) {
  if (line === "") continue;
  const bits = JSON.parse(line).map(h => BigInt("0x" + h));
  const runs = [];
  for (let k = 0; k < repeat; k++) runs.push(await call(bits));
  const times = runs.map(r => r.ms).sort((a, b) => a - b);
  console.log(JSON.stringify({ out: runs[0].ys, ms: times[Math.floor(times.length / 2)] }));
}
