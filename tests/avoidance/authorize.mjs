// Calls the exports of the avoidance module and prints each result.
//
//   node tests/avoidance/authorize.mjs MODULE < INPUTS > OUTPUTS
//
// Each input line is a JSON object.  {"xs": [...], "n": N} calls `authorize` with the array whose
// values have the given bit patterns, as 16 hexadecimal digits, and the panel count N, and the
// output line holds the bit patterns of the returned array and the time of the call in
// milliseconds.  {"box": [...], "n": N} calls `pcBox` with eleven values given by their bit
// patterns and N, and the output line holds the status and the bit patterns of `lo` and `hi`.
// Every call runs in a fresh instance of the module, whose allocator `alloc` places an input
// array: its length in the first word and its values after.

import { readFileSync } from "node:fs";
import readline from "node:readline";

const module = await WebAssembly.compile(readFileSync(process.argv[2]));

const hex = b => b.toString(16).padStart(16, "0");
const toFloat = h => new Float64Array(new BigUint64Array([BigInt("0x" + h)]).buffer)[0];
const floatBits = x => new BigUint64Array(new Float64Array([x]).buffer)[0];

async function authorize(bits, n) {
  const x = (await WebAssembly.instantiate(module)).exports;
  const ptr = x.alloc(BigInt(8 + 8 * bits.length));
  let view = new DataView(x.memory.buffer);
  view.setBigUint64(Number(ptr), BigInt(bits.length), true);
  bits.forEach((b, i) => view.setBigUint64(Number(ptr) + 8 + 8 * i, b, true));
  const start = performance.now();
  const out = Number(x.authorize(ptr, BigInt(n)));
  const ms = performance.now() - start;
  view = new DataView(x.memory.buffer);
  const len = Number(view.getBigUint64(out, true));
  const ys = [];
  for (let i = 0; i < len; i++) ys.push(hex(view.getBigUint64(out + 8 + 8 * i, true)));
  return { out: ys, ms };
}

async function pcBox(hs, n) {
  const x = (await WebAssembly.instantiate(module)).exports;
  const args = hs.map(toFloat);
  const r = x.pcBox(...args, BigInt(n));
  const [status, lo, hi] = r;
  return { status: Number(status), lo: hex(floatBits(lo)), hi: hex(floatBits(hi)) };
}

const lines = readline.createInterface({ input: process.stdin });
for await (const line of lines) {
  if (line === "") continue;
  const q = JSON.parse(line);
  if (q.xs !== undefined) {
    console.log(JSON.stringify(await authorize(q.xs.map(h => BigInt("0x" + h)), q.n)));
  } else {
    console.log(JSON.stringify(await pcBox(q.box, q.n)));
  }
}
