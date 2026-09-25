#!/usr/bin/env node
'use strict';
const fs = require('node:fs');
const path = require('node:path');
const { spawnSync } = require('node:child_process');

const root = path.resolve(__dirname, '..');
const artifacts = path.join(root, '.lake', 'arithmetic-check');
fs.mkdirSync(artifacts, { recursive: true });
function lean(label, args, timeout = 120, expectedFailure = false) {
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
  if (expectedFailure ? result.status === 0 : result.status !== 0) {
    throw new Error(`${label}: exit ${result.status}\n${output.slice(-12000)}`);
  }
  console.log(`${label}: ${expectedFailure ? 'rejected as required' : 'passed'}`);
  return { output, stdout };
}
function proof() {
  const { output } = lean('compiler-proof', ['lake', '-d', 'proofs/talos/lean', 'build',
    'Project.Compiler.ArithmeticCompilerAudit'], 900);
  for (const name of ['compileEnvironment_correct', 'compileEnvironment_sound']) {
    const match = output.match(new RegExp("'Project\\.Compiler\\.ArithmeticModule\\." +
      name + "' depends on axioms:\\s*\\[([^\\]]*)\\]"));
    if (!match || match[1].split(',').some(x =>
      !['propext', 'Classical.choice', 'Quot.sound'].includes(x.trim()))) {
      throw new Error(`missing or unexpected axiom audit for ${name}`);
    }
  }
  const negative = lean('kernel-negative', ['lake', '-d', 'proofs/talos/lean', 'env', 'lean',
    path.join(root, 'test/negative/arithmetic_kernel.lean')], 30, true);
  if (!negative.output.includes('(kernel) declaration type mismatch')) {
    throw new Error('negative equality did not fail at kernel checking');
  }
}
function engine() {
  lean('cli-build', ['lake', 'build', 'lean-wasm'], 600);
  lean('admission-regression', ['lake', 'env', 'lean', 'test/arithmetic_mode.lean'], 60);
  const fixture = path.join(root, '.lake/build/lib/lean/test/ArithmeticMilestone.olean');
  fs.mkdirSync(path.dirname(fixture), { recursive: true });
  lean('fixture', ['lake', 'env', 'lean', '-o', fixture, 'test/ArithmeticMilestone.lean'], 60);
  const expected = lean('native-results', ['lake', 'env', 'lean', '--run', 'test/ArithmeticMilestone.lean'], 60);
  const rows = expected.stdout.trim().split('\n').map(JSON.parse);
  fs.writeFileSync(path.join(artifacts, 'expected.jsonl'), rows.map(x => JSON.stringify(x)).join('\n') + '\n');
  for (const name of new Set(rows.map(x => x.name))) {
    lean(`compile-${name}`, ['lake', 'env', path.join(root, '.lake/build/bin/lean-wasm'),
      'compile-arithmetic', '--module', 'test.ArithmeticMilestone',
      '--entry', `ArithmeticMilestone.${name}`, '--out', path.join(artifacts, `${name}.wasm`)], 60);
  }
  const result = spawnSync(process.execPath, ['test/arithmetic_engine.mjs', artifacts], {
    cwd: root, encoding: 'utf8', timeout: 30000,
  });
  fs.writeFileSync(path.join(artifacts, 'engine.log'), (result.stdout || '') + (result.stderr || ''));
  if (result.error) throw result.error;
  if (result.status !== 0) throw new Error(result.stderr || 'independent engine check failed');
  process.stdout.write(result.stdout);
}
try {
  const mode = process.argv[2] || 'all';
  if (!['all', 'proof', 'engine'].includes(mode)) throw new Error('usage: tools/arithmetic-check.js [all|proof|engine]');
  if (mode === 'all' || mode === 'proof') proof();
  if (mode === 'all' || mode === 'engine') engine();
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
