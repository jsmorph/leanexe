#!/usr/bin/env node
import { readFile, writeFile } from 'node:fs/promises';
import { createInterface } from 'node:readline';
import { WasmHost, parse, parseWords } from '../tests/gpt32/browser/hosts.js';

if (process.argv.length !== 3 || process.argv[2] !== 'session')
  throw Error('usage: gpt32-wasm-host.mjs session');
const modulePath = process.env.LEANEXE_GPT32_WASM;
if (!modulePath) throw Error('LEANEXE_GPT32_WASM must name the Wasm module');
const { instance } = await WebAssembly.instantiate(await readFile(modulePath));
const host = new WasmHost(instance.exports);

for await (const line of createInterface({ input: process.stdin })) {
  const { command, args } = parse(line);
  if (command === 'quit') break;
  if (command === 'load') host.load(args[0], await readFile(args[1]));
  else if (command === 'words') host.words(args[0], parseWords(args[1]));
  else if (command === 'output') host.output(args[0], Number(args[1]));
  else if (command === 'shader') {
    if (!args[0].startsWith('@')) throw Error(`invalid shader name: ${args[0]}`);
  } else if (command === 'run') host.run(args[0], Number(args[1]), args[2], args.slice(3));
  else if (command === 'read') {
    const value = host.values.get(args[0]);
    if (value?.array === undefined) throw Error(`no array named ${args[0]}`);
    const n = Number(new DataView(host.x.memory.buffer).getBigUint64(value.array, true));
    await writeFile(args[1], host.bytes(value.array, 8 * (n + 1)));
  } else throw Error(`unknown command: ${line}`);
  process.stdout.write('ok\n');
}
host.close();
