// Test-only Wasm bindings. Test vectors and expected arithmetic live in Python.
import fs from "node:fs";
const [modulePath, inputPath, outputPath] = process.argv.slice(2);
const input = JSON.parse(fs.readFileSync(inputPath, "utf8"));
const { instance: { exports: w } } = await WebAssembly.instantiate(fs.readFileSync(modulePath));
function array(values) {
  const pointer = Number(w.alloc(BigInt(8 + values.length * 8))), view = new DataView(w.memory.buffer);
  view.setBigUint64(pointer, BigInt(values.length), true);
  values.forEach((v, i) => view.setBigUint64(pointer + 8 + i * 8, BigInt(v), true));
  return BigInt(pointer);
}
w.reset();
const args = [BigInt(input.op), array(input.x), array(input.aux), array(input.params), BigInt(input.position)];
const pointer = Number(w.compute(...args)), view = new DataView(w.memory.buffer), length = Number(view.getBigUint64(pointer, true));
if (length > 50257 || pointer + 8 + length * 8 > w.memory.buffer.byteLength) throw Error("Wasm result bounds");
fs.writeFileSync(outputPath, JSON.stringify(Array.from({ length }, (_, i) => view.getBigUint64(pointer + 8 + i * 8, true).toString())));
