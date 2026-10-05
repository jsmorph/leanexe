import assert from 'node:assert/strict';
import {mkdirSync, readFileSync, writeFileSync} from 'node:fs';
import {spawnSync} from 'node:child_process';
import {sourceCases, rejectedSources} from './source-cases.mjs';

const directory = 'build/scheme/source';
mkdirSync(directory, {recursive: true});
const scheme = process.env.SCHEME ?? 'chibi-scheme';
function compile(source, name) {
  const path = `${directory}/${name}.scm`;
  writeFileSync(path, source);
  const result = spawnSync(scheme, ['tools/scheme-compile.scm', path],
    {encoding: 'utf8', timeout: 10000});
  if (result.error) throw result.error;
  return result;
}
const compiled = sourceCases.map(({source, ...c}) => {
  const result = compile(source, c.name);
  assert.equal(result.status, 0, `${c.name}: ${result.stderr}`);
  const code = JSON.parse(result.stdout);
  assert(Array.isArray(code) && code.every(word => typeof word === 'string' &&
    /^\d+$/.test(word) && BigInt(word) < (1n << 64n)), `${c.name}: invalid words`);
  writeFileSync(`${directory}/${c.name}.json`, JSON.stringify(code) + '\n');
  return {capacity: 64, fuel: 300000, kind: 1, error: 0,
    ...c, name: `source-${c.name}`, code};
});
for (const [i, source] of rejectedSources.entries()) {
  const result = compile(source, `rejected-${i}`);
  assert.notEqual(result.status, 0, `compiler accepted ${source}`);
}
const corpusPath = 'build/scheme/corpus.json';
const corpus = JSON.parse(readFileSync(corpusPath)).filter(c => !c.name.startsWith('source-'));
writeFileSync(corpusPath, JSON.stringify([...corpus, ...compiled]) + '\n');
console.log(`Compiler: ${compiled.length} source programs compiled; ${rejectedSources.length} invalid programs rejected`);
