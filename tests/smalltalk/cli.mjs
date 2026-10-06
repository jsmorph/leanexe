import assert from 'node:assert/strict';
import {spawnSync} from 'node:child_process';
const module='build/smalltalk/smalltalk.wasm',examples='tests/smalltalk/examples/';
const run=(file,flags=[])=>spawnSync('node',
  ['tools/smalltalk-run.mjs',module,examples+file,...flags],{encoding:'utf8',timeout:5000});
for(const [file,flags,result] of [['count.st',[],'1000'],['escape.st',['--stress'],'42']]) {
  const r=run(file,flags);assert.equal(r.status,0,r.stderr);assert.equal(r.stdout.trim(),result);
}
const rejected=[['--fuel','-1'],['--fuel','18446744073709551616'],['--fuel'],
  ['--fuel','word'],['--capacity','-1'],['--capacity','18446744073709551616'],
  ['--capacity'],['--unknown']];
for(const flags of rejected) {
  const r=run('escape.st',flags);assert.equal(r.error,undefined,'CLI timed out');
  assert.equal(r.status,1);assert.match(r.stderr,/unsigned 64-bit integer|unknown option/);
}
const fuel=run('escape.st',['--fuel','0']);
assert.equal(fuel.status,1);assert.match(fuel.stderr,/instruction fuel exhausted/);
console.log(`CLI: 2 examples; ${rejected.length} invalid options; zero-fuel rejection`);
