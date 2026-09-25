import { readFileSync } from 'node:fs';
import { resolve } from 'node:path';

const directory = process.argv[2];
if (!directory || process.argv.length !== 3) throw new Error('usage: node test/arithmetic_engine.mjs <artifact-directory>');
const cases = readFileSync(resolve(directory, 'expected.jsonl'), 'utf8').trim().split('\n').map(JSON.parse);
const entries = ['constant', 'wrapping', 'quotient', 'remainder', 'shifts', 'nested', 'order',
  'bindings', 'shadowed', 'nestedBindings', 'unusedBinding', 'boundConstant',
  'compareEq', 'compareLt', 'compareLe', 'compareBEq', 'compareBNe',
  'nestedChoice', 'choiceBindings', 'choiceOperands',
  'doReturn', 'doBind', 'doUpdates', 'doEarly', 'doNested', 'doBranches', 'doConstant',
  'localFunction', 'capturedShadow', 'chainedFunctions', 'nestedFunctions',
  'unusedFunction', 'doJoined', 'doBranchUpdates'];
const constants = new Set(['constant', 'boundConstant', 'doConstant']);
const counts = new Map(entries.map(name => [name, new Set()]));
const uint64 = value => typeof value === 'string' && /^(0|[1-9][0-9]*)$/.test(value) &&
  BigInt(value) < (1n << 64n);
for (const row of cases) {
  if (!counts.has(row.name) || !Array.isArray(row.args) ||
      row.args.length !== (constants.has(row.name) ? 0 : 2) ||
      !row.args.every(uint64) || !uint64(row.expected)) {
    throw new Error(`invalid native result: ${JSON.stringify(row)}`);
  }
  const key = row.args.join(',');
  if (counts.get(row.name).has(key)) throw new Error(`duplicate input for ${row.name}: ${key}`);
  counts.get(row.name).add(key);
}
for (const [name, inputs] of counts) {
  if (inputs.size !== (constants.has(name) ? 1 : 14)) {
    throw new Error(`incomplete native results for ${name}: ${inputs.size} inputs`);
  }
}
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
