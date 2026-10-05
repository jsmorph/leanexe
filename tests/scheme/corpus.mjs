// Shared native/WASM bytecode corpus. This assembler only resolves labels and descriptors.
import {mkdirSync, writeFileSync} from 'node:fs';
import {fileURLToPath} from 'node:url';

const ops = Object.fromEntries(
  'word bool unit callcc load store close drop jump branch binary call tailcall ret global'
    .split(' ').map((name, i) => [name, i]));

class Program {
  instructions = []; labels = new Map(); descriptors = [];
  label(name) { this.labels.set(name, this.instructions.length); return this; }
  emit(op, a = 0, b = 0) { this.instructions.push([ops[op], a, b, 0]); return this; }
  close(entry, params = [], captures = []) {
    const desc = this.descriptors.length;
    this.descriptors.push([params.length, ...params, captures.length, ...captures]);
    return this.emit('close', entry, {desc});
  }
  global(name, value = null) {
    return this.emit(value === null ? 'unit' : 'word', value ?? 0)
      .emit('global', name).emit('drop');
  }
  code() {
    const starts = []; let next = 1 + 4 * this.instructions.length;
    for (const desc of this.descriptors) { starts.push(next); next += desc.length; }
    const resolve = x => {
      if (typeof x === 'string') {
        if (!this.labels.has(x)) throw new Error(`unknown label ${x}`);
        return this.labels.get(x);
      }
      return typeof x === 'object' ? starts[x.desc] : x;
    };
    return [this.instructions.length, ...this.instructions.flatMap(i => i.map(resolve)),
      ...this.descriptors.flat()].map(String);
  }
}

export const cases = [];
function test(name, p, expected, options = {}) {
  cases.push({name, code: p.code(), capacity: 64, fuel: 300000,
    expected: String(expected), kind: 1, error: 0, ...options});
}
const p = () => new Program();
test('arithmetic', p().emit('word', 100).emit('word', 23).emit('binary', 0).emit('ret'), 123);
test('word-wrap', p().emit('word', 18446744073709551615n).emit('word', 1)
  .emit('binary', 0).emit('ret'), 0);
test('argument-order', p().close('subtract', [1, 2]).emit('word', 10).emit('word', 3)
  .emit('call', 2).emit('ret').label('subtract').emit('load', 1).emit('load', 2)
  .emit('binary', 1).emit('ret'), 7);
test('pending-operand', p().emit('word', 100).close('fn').emit('call', 0)
  .emit('binary', 0).emit('ret').label('fn').emit('word', 23).emit('ret'), 123);
test('shadowing', p().global(1, 42).close('fn', [1]).emit('word', 3).emit('call', 1)
  .emit('drop').emit('load', 1).emit('ret').label('fn').emit('load', 1).emit('ret'), 42);
test('shared-mutation', p().global(1, 1).global(2).close('getter', [], [1])
  .emit('store', 2).emit('drop').emit('word', 9).emit('store', 1).emit('drop')
  .emit('load', 2).emit('tailcall', 0).label('getter').emit('load', 1).emit('ret'), 9);

function countdown(n) {
  return p().global(2).close('fn', [1], [2]).emit('store', 2).emit('drop')
    .emit('load', 2).emit('word', n).emit('tailcall', 1).label('fn')
    .emit('load', 1).emit('word', 0).emit('binary', 3).emit('branch', 'again')
    .emit('word', 7).emit('ret').label('again').emit('load', 2).emit('load', 1)
    .emit('word', 1).emit('binary', 1).emit('tailcall', 1);
}
test('tail-10000', countdown(10000), 7, {capacity: 32, tail: true});
test('tail-100', countdown(100), 7, {capacity: 32, tail: true});
test('tail-under-caller', p().global(2).close('fn', [1], [2]).emit('store', 2)
  .emit('drop').emit('word', 100).close('caller', [], [2]).emit('call', 0)
  .emit('binary', 0).emit('ret').label('caller').emit('load', 2).emit('word', 100)
  .emit('tailcall', 1).label('fn').emit('load', 1).emit('word', 0)
  .emit('binary', 3).emit('branch', 'again').emit('word', 7).emit('ret')
  .label('again').emit('load', 2).emit('load', 1).emit('word', 1)
  .emit('binary', 1).emit('tailcall', 1), 107);
test('nested-escape', p().emit('word', 100).emit('callcc').close('callback', [1])
  .emit('call', 1).emit('binary', 0).emit('ret').label('callback')
  .close('inner', [], [1]).emit('call', 0).emit('word', 999).emit('ret')
  .label('inner').emit('load', 1).emit('word', 7).emit('call', 1)
  .emit('word', 999).emit('ret'), 107);

test('multi-shot', p().global(1, 0).global(2).global(4).emit('word', 100)
  .emit('callcc').close('callback', [3], [2]).emit('call', 1)
  .emit('binary', 0).emit('store', 4).emit('drop').emit('load', 1)
  .emit('word', 2).emit('binary', 2).emit('branch', 'finish')
  .emit('load', 1).emit('word', 1).emit('binary', 0).emit('store', 1).emit('drop')
  .emit('load', 2).emit('load', 1).emit('tailcall', 1).label('finish')
  .emit('load', 4).emit('ret').label('callback').emit('load', 3).emit('store', 2)
  .emit('drop').emit('word', 10).emit('ret'), 102, {counter: '2'});
test('callcc-callback', p().emit('callcc').emit('callcc').emit('tailcall', 1), 0, {kind: 6});
test('only-false-is-false', p().emit('word', 0).emit('branch', 'bad')
  .emit('word', 7).emit('ret').label('bad').emit('word', 999).emit('ret'), 7);
test('false-branch', p().emit('bool', 0).emit('branch', 'yes').emit('word', 999)
  .emit('ret').label('yes').emit('word', 7).emit('ret'), 7);
test('bad-pc', p().emit('jump', 200), 0, {error: 1});
test('unbound', p().emit('load', 99), 0, {error: 2});
test('underflow', p().emit('ret'), 0, {error: 4});
test('expected-words', p().emit('bool', 1).emit('word', 3).emit('binary', 0), 0, {error: 5});
test('bad-tail-boundary', p().emit('word', 100).close('fn').emit('tailcall', 0)
  .label('fn').emit('word', 7).emit('ret'), 0, {error: 6});
test('not-callable', p().emit('word', 3).emit('tailcall', 0), 0, {error: 7});
test('closure-arity', p().close('fn', [1]).emit('tailcall', 0).label('fn')
  .emit('word', 7).emit('ret'), 0, {error: 8});
test('callcc-arity', p().emit('callcc').emit('tailcall', 0), 0, {error: 8});
test('capture-unbound', p().close('fn', [], [99]).emit('ret').label('fn')
  .emit('word', 7).emit('ret'), 0, {error: 2});
test('live-heap-oom', p().emit('word', 1).emit('word', 2).emit('word', 3), 0,
  {capacity: 8, error: 9});
test('binding-reservation-oom', p().close('fn', [1, 2]).emit('word', 1)
  .emit('word', 2).emit('tailcall', 2).label('fn').emit('load', 1).emit('ret'), 0,
  {capacity: 12, error: 9});
cases.push({name: 'malformed-code', code: ['1'], capacity: 32, fuel: 100,
  expected: '0', kind: 1, error: 10});
cases.push({name: 'malformed-descriptor', code: ['1', '6', '0', '999', '0'], capacity: 32,
  fuel: 100, expected: '0', kind: 1, error: 10});
cases.push({name: 'empty-code', code: [], capacity: 32, fuel: 100,
  expected: '0', kind: 1, error: 10});
cases.push({name: 'unknown-opcode', code: ['1', '99', '0', '0', '0'], capacity: 32,
  fuel: 100, expected: '0', kind: 1, error: 10});

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  mkdirSync(new URL('../../build/scheme/', import.meta.url), {recursive: true});
  writeFileSync(new URL('../../build/scheme/corpus.json', import.meta.url),
    JSON.stringify(cases) + '\n');
}
