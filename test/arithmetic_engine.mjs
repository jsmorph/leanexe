import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const directory = process.argv[2];
if (!directory) throw new Error('usage: node test/arithmetic_engine.mjs <artifact-directory>');
const cases = readFileSync(resolve(directory, 'expected.jsonl'), 'utf8').trim().split('\n').map(JSON.parse);
const modules = new Map();
for (const row of cases) {
  if (!modules.has(row.name)) {
    const bytes = readFileSync(resolve(directory, `${row.name}.wasm`));
    if (!WebAssembly.validate(bytes)) throw new Error(`invalid module: ${row.name}`);
    modules.set(row.name, new WebAssembly.Instance(new WebAssembly.Module(bytes)).exports);
  }
  const invoke = modules.get(row.name)[row.name];
  if (typeof invoke !== 'function') throw new Error(`missing export: ${row.name}`);
  const actual = BigInt.asUintN(64, invoke(...row.args.map(BigInt))).toString();
  if (actual !== row.expected) {
    throw new Error(`${row.name}(${row.args.join(', ')}): expected ${row.expected}, received ${actual}`);
  }
}
console.log(`Passed ${cases.length} native Lean / independent Wasm engine comparisons across ${modules.size} declarations.`);
