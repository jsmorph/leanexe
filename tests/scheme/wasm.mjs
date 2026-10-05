import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {Host, cell} from '../../tools/scheme-host.mjs';
const cases = JSON.parse(readFileSync(process.argv[4] ?? 'build/scheme/corpus.json'));

const bytes = readFileSync(process.argv[2] ?? 'build/scheme/scheme.wasm');
assert(WebAssembly.validate(bytes), 'WASM validation failed');
const module = await WebAssembly.compile(bytes);
assert.equal(WebAssembly.Module.imports(module).length, 0, 'unexpected WASM imports');
const instantiate = async () => (await WebAssembly.instantiate(module)).exports;


function children(s, h) {
  const tag = Number(cell(s, h, 0));
  if (tag === 5) return [cell(s, h, 4)];
  if (tag === 6 || tag === 10) return [cell(s, h, 2)];
  if (tag === 7) return [cell(s, h, 2), cell(s, h, 3)];
  if (tag === 8 || tag === 9) return [cell(s, h, 3), cell(s, h, 4)];
  assert(tag >= 1 && tag <= 4, `bad reachable cell kind ${tag}`);
  return [];
}
function arenaCheck(s, swept = false) {
  const cap = Number(s[14]), free = new Set();
  for (let h = s[8]; h !== 0n; h = cell(s, h, 2)) {
    assert(h > 0n && h <= BigInt(cap) && !free.has(h), 'invalid free list');
    assert.equal(cell(s, h, 0), 0n); free.add(h);
  }
  assert.equal(BigInt(free.size), s[9], 'wrong free count');
  for (let h = 1n; h <= BigInt(cap); h++)
    assert.equal(cell(s, h, 0) === 0n, free.has(h), 'missing/extra free cell');
  const roots = [1n, 2n, 3n, 4n, s[2], s[3], s[16]];
  if (s[0] === 1n) roots.push(s[4], s[5]);
  if (s[0] === 2n || s[0] === 3n) roots.push(s[7]);
  const live = new Set();
  while (roots.length) {
    const h = roots.pop();
    if (h === 0n || live.has(h)) continue;
    assert(h > 0n && h <= BigInt(cap) && !free.has(h), `dangling root/edge ${h}`);
    live.add(h); roots.push(...children(s, h));
  }
  if (swept) assert.equal(live.size + free.size, cap, 'garbage survived collection');
  if (s[0] !== 4n) assert.equal(s[19] + s[20], 0n, 'scratch roots escaped transition');
  return live;
}
function frames(s) {
  let count = 0, h = s[3]; const seen = new Set();
  while (h !== 0n) {
    assert(!seen.has(h), 'cyclic stack'); seen.add(h);
    const tag = cell(s, h, 0);
    assert(tag === 7n || tag === 8n);
    if (tag === 8n) count++;
    h = cell(s, h, tag === 8n ? 4 : 3);
  }
  return count;
}

// The optional native snapshot comparison covers every register, cell, and worklist word.
const nativePath = process.argv[3];
const native = nativePath ? JSON.parse(readFileSync(nativePath)) : null;
let passed = 0;
for (const c of cases) for (const stress of [0, 1]) {
  const host = new Host(await instantiate()), x = host.x;
  const code = host.array(c.code);
  let s = x.init(BigInt(c.capacity), BigInt(stress));
  const initialPtr = s, initialMemory = x.memory.buffer.byteLength;
  const allocations = x.allocCount.value;
  s = x.run(code, s, BigInt(c.fuel));
  assert.equal(x.allocCount.value, allocations, `${c.name}: VM allocated outside its arena`);
  assert.equal(s, initialPtr, `${c.name}: state buffer was copied`);
  assert.equal(x.memory.buffer.byteLength, initialMemory, `${c.name}: linear memory grew`);
  let state = host.words(s);
  assert.equal(Number(state[15]), c.error, c.name);
  if (!c.error) {
    assert.equal(state[0], 3n, `${c.name}: fuel exhausted`);
    assert.equal(Number(cell(state, state[7], 0)), c.kind, c.name);
    assert.equal(BigInt.asUintN(64, x.resultWord(s)), BigInt(c.expected), c.name);
    if (c.counter) {
      const loc = x.lookup(s, state[16], 1n);
      assert.equal(cell(state, cell(state, loc, 2), 2), BigInt(c.counter));
    }
  }
  arenaCheck(state);
  s = x.collect(s); state = host.words(s);
  arenaCheck(state, !c.error);
  if (native) {
    const expected = native.find(n => n.name === c.name && n.stress === stress);
    assert(expected, `missing native result ${c.name}/${stress}`);
    assert.deepEqual(state.map(String), expected.state, `${c.name}/${stress}: native/WASM mismatch`);
  }
  if (c.name === 'binding-reservation-oom')
    assert(!Array.from({length: c.capacity}, (_, i) => cell(state, BigInt(i + 1), 0))
      .includes(10n), 'OOM installed a partial parameter binding');
  console.log(`wasm ${c.name}, stress=${stress}: ok, gc=${state[11]}, peak=${state[13]}/${c.capacity}`);
  host.release(s); host.release(code);
  assert.equal(host.outstanding(), 0n, 'host allocator leaked an array');
  passed++;
}

// Inspect every transition for shorter programs, including each phase's root set.
for (const c of cases.filter(c => !c.error && !c.skipSteps && c.name !== 'tail-10000')) {
  const host = new Host(await instantiate()), x = host.x, code = host.array(c.code);
  let s = x.init(BigInt(c.capacity), 1n), peakFrames = 0, steps = 0;
  while (host.words(s)[0] < 3n && steps < c.fuel) {
    s = x.step(code, s); const state = host.words(s);
    arenaCheck(state); peakFrames = Math.max(peakFrames, frames(state)); steps++;
  }
  assert.equal(host.words(s)[0], 3n, `${c.name}: stepped run failed`);
  if (c.tail) assert.equal(peakFrames, 0, 'tail call added a return frame');
  if (c.name === 'tail-under-caller') assert.equal(peakFrames, 1);
  if (c.name === 'nested-escape') assert.equal(peakFrames, 3);
  host.release(s); host.release(code); assert.equal(host.outstanding(), 0n); passed++;
}

// Collector graph tests use its real exported allocator; JS supplies only fixtures and an oracle.
{
  const host = new Host(await instantiate()), x = host.x;
  let s = x.init(32n, 0n);
  const put = (i, value) => { s = x.write(s, BigInt(i), value); };
  const alloc = (tag, a = 0n, b = 0n, c = 0n) => {
    s = x.allocate(s, tag, a, b, c); return host.words(s)[10];
  };
  // A location -> closure -> environment -> location cycle.
  const loc = alloc(10n, 3n), env = alloc(9n, 99n, loc), closure = alloc(5n, 123n, 456n, env);
  put(24 + 5 * (Number(loc) - 1) + 2, closure);
  put(16, env); s = x.collect(s);
  assert.equal(arenaCheck(host.words(s), true).size, 7, 'rooted cycle was lost');
  put(16, 0n); s = x.collect(s);
  assert.equal(arenaCheck(host.words(s), true).size, 4, 'unreachable cycle leaked');
  // A word payload that numerically equals a handle is not a pointer.
  const dead = alloc(1n, 123n), number = alloc(1n, dead);
  put(0, 3n); put(7, number); s = x.collect(s);
  assert.equal(cell(host.words(s), dead, 0), 0n, 'numeric payload retained garbage');
  assert.equal(arenaCheck(host.words(s), true).size, 5);
  // Closure code addresses and symbol names are not pointers either.
  put(0, 0n); put(7, 0n); put(16, 0n); s = x.collect(s);
  const junk = alloc(1n, 999n), c = alloc(5n, junk, junk, 0n), l = alloc(10n, c);
  const e = alloc(9n, junk, l, 0n); put(16, e); s = x.collect(s);
  assert.equal(cell(host.words(s), junk, 0), 0n, 'code/symbol scalar was traced');
  arenaCheck(host.words(s), true);
  // In exec phase, old procedure/argument/result registers are not roots.
  const inactive = alloc(1n, 77n);
  put(4, inactive); put(5, inactive); put(7, inactive); s = x.collect(s);
  assert.equal(cell(host.words(s), inactive, 0), 0n, 'inactive register retained garbage');
  arenaCheck(host.words(s), true);
  const before = host.words(s); s = x.collect(s); const after = host.words(s);
  assert.equal(after[9], before[9]); // A second collection has the same live/free partition.
  host.release(s); assert.equal(host.outstanding(), 0n); passed += 6;
}

{
  const host = new Host(await instantiate()), x = host.x;
  let s = x.init(16n, 0n); s = x.write(s, 2n, 17n); s = x.collect(s);
  assert.equal(host.words(s)[15], 3n, 'bad root was not rejected');
  const failed = host.words(s); s = x.collect(s);
  assert.deepEqual(host.words(s), failed, 'collection changed a terminal error');
  host.release(s); assert.equal(host.outstanding(), 0n); passed++;
}

// A saved continuation remains callable after completion and explicit collection, repeatedly.
{
  const c = cases.find(c => c.name === 'multi-shot');
  const host = new Host(await instantiate()), x = host.x, code = host.array(c.code);
  let s = x.run(code, x.init(64n, 1n), BigInt(c.fuel));
  for (const value of [10n, 20n, 30n]) {
    s = x.collect(s);
    const state = host.words(s), savedLoc = x.lookup(s, state[16], 2n);
    const continuation = cell(state, savedLoc, 2);
    s = x.reserve(s, 2n); s = x.allocate(s, 1n, value, 0n, 0n);
    const argument = host.words(s)[10]; s = x.operand(s, argument, 0n);
    s = x.setApply(s, continuation, host.words(s)[10], 1n, 0n);
    s = x.run(code, s, BigInt(c.fuel));
    assert.equal(BigInt.asUintN(64, x.resultWord(s)), 100n + value);
    const done = host.words(s), counterLoc = x.lookup(s, done[16], 1n);
    assert.equal(cell(done, cell(done, counterLoc, 2), 2), 2n, 'continuation rolled back mutation');
    arenaCheck(done); passed++;
  }
  host.release(s); host.release(code); assert.equal(host.outstanding(), 0n);
}
console.log(`WASM: ${passed} checks passed; ${native ? `${cases.length * 2} full native-state comparisons; ` : ''}${bytes.length} bytes`);
