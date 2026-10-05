// Run compiler output on the actual VM/GC WASM binary.
import {readFileSync} from 'node:fs';
import {Host, cell} from './scheme-host.mjs';

const [codePath, capacity = '64', fuel = '300000', stress = '0'] = process.argv.slice(2);
if (!codePath) throw new Error('usage: node tools/scheme-run.mjs CODE.json [CAPACITY] [FUEL] [STRESS]');
const wasm = process.env.SCHEME_WASM ?? 'build/scheme/scheme.wasm';
const {instance} = await WebAssembly.instantiate(readFileSync(wasm));
const host = new Host(instance.exports), x = host.x;
const code = host.array(JSON.parse(readFileSync(codePath)));
let s = x.init(BigInt(capacity), BigInt(stress));
try {
  s = x.run(code, s, BigInt(fuel));
  const state = host.words(s);
  if (state[0] === 4n) throw new Error(`VM error ${state[15]} at instruction ${state[1]}`);
  if (state[0] !== 3n) throw new Error('execution fuel exhausted');
  const tag = cell(state, state[7], 0), value = cell(state, state[7], 2);
  console.log(tag === 1n ? String(value) : tag === 2n ? (value === 0n ? '#f' : '#t') :
    tag === 3n ? '#<unspecified>' : tag === 6n ? '#<continuation>' : '#<procedure>');
} finally {
  host.release(s); host.release(code);
}
