#!/usr/bin/env node
'use strict';
const fs = require('node:fs');
const path = require('node:path');
const { spawnSync } = require('node:child_process');

const root = path.resolve(__dirname, '..');
const groups = require('../test/arithmetic-engine-groups.json');
const subset = process.argv[2] === 'subset-engine' ? process.argv[3] : null;
const validSubset = typeof subset === 'string' && /^[a-z][a-z0-9-]*$/.test(subset) &&
  Object.hasOwn(groups, subset);
const artifacts = path.join(root, '.lake', 'arithmetic-check',
  process.argv[2] === 'range-engine' ? 'range' : validSubset ? `subsets/${subset}` : '');
const rangeEntries = new Set(require('../test/arithmetic-range-cases.json'));
fs.mkdirSync(artifacts, { recursive: true });
function lean(label, args, timeout = 120) {
  const log = path.join(artifacts, `${label}.log`);
  const errors = path.join(artifacts, `${label}.stderr.log`);
  const out = fs.openSync(log, 'w');
  const err = fs.openSync(errors, 'w');
  let result;
  try {
    result = spawnSync(path.join(root, 'tools/leanrun'), ['--timeout', String(timeout), ...args], {
      cwd: root, env: process.env, stdio: ['ignore', out, err],
    });
  } finally {
    fs.closeSync(out);
    fs.closeSync(err);
  }
  const stdout = fs.readFileSync(log, 'utf8');
  const output = stdout + fs.readFileSync(errors, 'utf8');
  if (result.error) throw result.error;
  if (result.status !== 0) {
    throw new Error(`${label}: exit ${result.status}\n${output.slice(-12000)}`);
  }
  console.log(`${label}: passed`);
  return { output, stdout };
}
function proof() {
  lean('compiler-proof', ['lake', '-d', 'proofs/talos/lean', 'build',
    'Project.Compiler.ArithmeticCompilerAudit'], 900);
  const result = spawnSync('python3', ['tools/arithmetic-audit.py',
    path.join(artifacts, 'compiler-proof.log')], { cwd: root, encoding: 'utf8', timeout: 30000 });
  fs.writeFileSync(path.join(artifacts, 'axioms.log'), (result.stdout || '') + (result.stderr || ''));
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(result.stderr || 'arithmetic axiom audit failed');
  process.stdout.write(result.stdout);
}
function engine(suite = 'all') {
  const selected = suite === 'all' ? null : suite === 'range' ? rangeEntries : new Set(groups[suite]);
  if (selected && (selected.size === 0 || (suite !== 'range' && selected.size !== groups[suite].length))) {
    throw new Error(`empty or duplicate entries in execution group: ${suite}`);
  }
  lean('cli-build', ['lake', 'build', 'lean-wasm'], 600);
  lean('admission-test', ['lake', 'env', 'lean', 'test/arithmetic_mode.lean'], 60);
  lean('reserved-exports', ['lake', 'env', 'lean', 'test/arithmetic_reserved_exports.lean'], 60);
  const fixture = path.join(root, '.lake/build/lib/lean/test/ArithmeticMilestone.olean');
  fs.mkdirSync(path.dirname(fixture), { recursive: true });
  lean('fixture', ['lake', 'env', 'lean', '-o', fixture, 'test/ArithmeticMilestone.lean'], 60);
  const expected = lean('native-results', ['lake', 'env', 'lean', '--run', 'test/ArithmeticMilestone.lean'], 60);
  const rows = expected.stdout.trim().split('\n').map(JSON.parse)
    .filter(row => selected === null || selected.has(row.name));
  if (selected) {
    const present = new Set(rows.map(row => row.name));
    for (const name of selected) {
      if (!present.has(name)) throw new Error(`execution group ${suite} has no native fixture: ${name}`);
    }
  }
  fs.writeFileSync(path.join(artifacts, 'expected.jsonl'), rows.map(x => JSON.stringify(x)).join('\n') + '\n');
  for (const name of new Set(rows.map(x => x.name))) {
    lean(`compile-${name}`, ['lake', 'env', path.join(root, '.lake/build/bin/lean-wasm'),
      'compile-arithmetic', '--module', 'test.ArithmeticMilestone',
      '--entry', `ArithmeticMilestone.${name}`, '--out', path.join(artifacts, `${name}.wasm`)], 60);
  }
  const result = spawnSync(process.execPath, ['test/arithmetic_engine.mjs', artifacts, suite], {
    cwd: root, encoding: 'utf8', timeout: 30000,
  });
  fs.writeFileSync(path.join(artifacts, 'engine.log'), (result.stdout || '') + (result.stderr || ''));
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(result.stderr || 'independent engine check failed');
  process.stdout.write(result.stdout);
}
try {
  const mode = process.argv[2] || 'all';
  const ordinary = ['all', 'proof', 'engine', 'range-engine'].includes(mode);
  if ((!ordinary && mode !== 'subset-engine') ||
      (ordinary && process.argv.length > 3) ||
      (mode === 'subset-engine' && (process.argv.length !== 4 || !validSubset))) {
    throw new Error('usage: tools/arithmetic-check.js [all|proof|engine|range-engine|subset-engine <checked-group>]');
  }
  if (mode === 'all' || mode === 'proof') proof();
  if (mode === 'all' || mode === 'engine') engine();
  if (mode === 'range-engine') engine('range');
  if (mode === 'subset-engine') engine(subset);
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
