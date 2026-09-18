#!/usr/bin/env node
// Repeatable bounded compiler/proof/execution corpus. All generated files stay in build/.
'use strict';
const fs = require('node:fs');
const path = require('node:path');
const {spawnSync} = require('node:child_process');
const repo = path.resolve(__dirname, '../..');
const root = fs.mkdtempSync(path.join(repo, 'build/wgsl/body-check-'));
let sequence = 0;
let rejectedCases = 0;

function run(command, args, expectFailure = false, diagnostic = null) {
  const result = spawnSync(command, args, {cwd: repo, encoding: 'utf8', maxBuffer: 16*1024*1024});
  const output = (result.stdout || '') + (result.stderr || '');
  fs.writeFileSync(path.join(root, `${String(sequence++).padStart(2, '0')}.log`), output);
  if (result.error || result.signal || (expectFailure ? result.status === 0 : result.status !== 0)
      || (diagnostic && !output.includes(diagnostic))) {
    process.stderr.write(output);
    throw new Error(`Unexpected result: ${command} ${args.join(' ')} (${result.status}, ${result.signal})`);
  }
  return output;
}
function lean(args, failure = false, diagnostic = null) {
  return run(path.join(repo, 'tools/leanrun'), ['--timeout', '90s', 'lake', ...args], failure, diagnostic);
}
function negative(name, body, diagnostic) {
  const file = path.join(root, `${name}.lean`);
  const destination = path.join(root, name);
  fs.writeFileSync(file, `import LeanExe.WGSL.Examples.Body\nopen LeanExe.WGSL LeanExe.WGSL.Source\n${body(destination)}\n`);
  lean(['env', 'lean', file], true, diagnostic);
  if (fs.existsSync(destination)) throw new Error(`Rejected case wrote output: ${name}`);
  rejectedCases++;
}

try {
  console.log(`Body compiler corpus: ${root}`);
  lean(['build', 'LeanExe.WGSL.Examples.Body']);
  lean(['env', 'lean', '--run', 'tools/wgsl/body/Prepare.lean', root]);
  const cases = JSON.parse(fs.readFileSync(path.join(root, 'cases.json')));
  for (const {name} of cases) {
    const log = lean(['env', 'lean', path.join(root, `${name}.lean`)]);
    if (log.includes('sorryAx') || log.includes('Lean.ofReduceBool')) throw new Error('forbidden proof axiom');
    if ((log.match(/depends on axioms:|does not depend on any axioms/g) || []).length !== 3)
      throw new Error('missing proof audits');
    console.log(`Lean checked source equality, actual shader text and statement execution: ${name}`);
  }
  console.log(`Passed ${cases.length} source equality, shader parse and statement execution proofs.`);
  const independent = path.join(root, 'IndependentMatrix.lean');
  fs.writeFileSync(independent, 'import LeanExe.WGSL.Examples.Body\n' +
    fs.readFileSync(path.join(root, 'matmul/source-equality.lean.txt'), 'utf8') +
    '\n#print axioms LeanExe.WGSL.Examples.Body.matmul.wgslShaderParsed\n' +
    '#print axioms LeanExe.WGSL.Examples.Body.matmul.wgslSourceCorrect\n' +
    '#print axioms LeanExe.WGSL.Examples.Body.matmul.wgslExecutionCorrect\n');
  const independentLog = lean(['env', 'lean', independent]);
  if (independentLog.includes('sorryAx') || independentLog.includes('Lean.ofReduceBool'))
    throw new Error('forbidden independent proof axiom');
  console.log('Matrix proof rechecked without invoking the compiler.');
  lean(['-d', 'proofs/talos/lean', 'env', 'lean', '--run', path.join(repo, 'tools/wgsl/body/Vectors.lean'), path.join(root, 'vectors')]);
  for (const {name} of cases) {
    run(path.join(repo, 'tools/wgsl/run-macos-cpu.sh'), ['--body', path.join(root, name),
      '--vectors', path.join(root, 'vectors', `${name}.json`), '--report', path.join(root, name, 'execution.json')]);
    console.log(`CPU WebGPU matched original Lean words: ${name}`);
  }
  const report = name => JSON.parse(fs.readFileSync(path.join(root, name, 'execution.json')));
  for (const [a,b] of [['add','multiply'], ['matmul','sumProducts']]) {
    if (JSON.stringify(report(a).actual) === JSON.stringify(report(b).actual)) throw new Error('body mutation did not change output');
    if (fs.readFileSync(path.join(root,a,'kernel.wgsl'),'utf8') === fs.readFileSync(path.join(root,b,'kernel.wgsl'),'utf8'))
      throw new Error('body mutation did not change shader');
  }
  const compile = (definition, shape = '2 3 6 6') => dest => `${definition}\n#compile_wgsl bad ${shape} ${JSON.stringify(dest)}`;
  negative('unmarked', compile('def bad : Kernel := fun ar a b r c => ar.add (a (r*3+c)) (b (r*3+c))'), 'mark the definition');
  negative('signature', compile('@[wgsl] def bad : Nat := 1'), 'entry must have type');
  negative('integer-arithmetic', compile('@[wgsl] def bad : Kernel := fun _ a b _ _ => a 0 + b 0'), 'unsupported word expression');
  negative('branch', compile('@[wgsl] def bad : Kernel := fun _ a b r _ => if r == 0 then a 0 else b 0'), 'unsupported word expression');
  negative('dynamic-fold', compile('@[wgsl] def bad : Kernel := fun ar a _ r _ => Source.fold r 0 (fun k acc => ar.add acc (a k))'), 'nonliteral fold count');
  negative('out-of-bounds', compile('@[wgsl] def bad : Kernel := fun _ a _ r c => a (r*3+c+1)'), 'A index may be out of bounds');
  negative('overflow', compile('@[wgsl] def bad : Kernel := fun _ a _ r _ => a (4294967295+r)'), 'index addition may overflow');
  negative('zero-dimension', compile('@[wgsl] def bad : Kernel := fun _ a _ _ _ => a 0', '0 3 6 6'), 'dimensions must be positive');
  for (const [name, word] of [['positive-infinity','0x7f800000'], ['negative-infinity','0xff800000'],
    ['quiet-nan','0x7fc00000'], ['signaling-nan','0x7f800001']])
    negative(name, compile(`@[wgsl] def bad : Kernel := fun _ _ _ _ _ => ${word}`), 'nonfinite word literal');
  negative('custom-nat-add', compile('def alteredAdd : HAdd Nat Nat Nat := ⟨Nat.mul⟩\n' +
    '@[wgsl] def bad : Kernel := fun _ a _ r c => a (@HAdd.hAdd Nat Nat Nat alteredAdd r c)'),
    'source equality did not pass');

  const original = fs.readFileSync(path.join(root, 'add', 'kernel.wgsl'), 'utf8');
  const matrix = fs.readFileSync(path.join(root, 'matmul', 'kernel.wgsl'), 'utf8');
  const mutations = [
    ['wrong-operation', 'add', '2 3 6 6', original.replace('v0 + v1', 'v0 * v1'), 'source equality did not pass'],
    ['wrong-store', 'add', '2 3 6 6', original.replace('c[row * N + col]', 'c[col * M + row]'), 'failed independent parsing'],
    ['missing-guard', 'add', '2 3 6 6', original.replace('if (col >= N || row >= M) { return; }', ''), 'failed independent parsing'],
    ['trailing-store', 'add', '2 3 6 6', original + '\nc[0u] = 0.0f;\n', 'trailing tokens'],
    ['wrong-loop-count', 'matmul', '2 3 8 12', matrix.replace('< 4u', '< 3u'), 'source equality did not pass'],
    ['wrong-initial-word', 'matmul', '2 3 8 12', matrix.replace('bitcast<f32>(0u)', 'bitcast<f32>(1065353216u)'), 'source equality did not pass'],
    ['wrong-increment', 'matmul', '2 3 8 12', matrix.replace('k2 + 1u', 'k2 + 2u'), 'failed independent parsing'],
    ['wrong-loop-start', 'matmul', '2 3 8 12', matrix.replace('k2: u32 = 0u', 'k2: u32 = 1u'), 'failed independent parsing'],
    ['wrong-loop-assignment', 'matmul', '2 3 8 12', matrix.replace('acc1 = v6;', 'v0 = v6;'), 'expected loop accumulator assignment'],
    ['escaped-local', 'matmul', '2 3 8 12', matrix.replace('c[row * N + col] = acc1;', 'c[row * N + col] = v6;'), 'undefined word'],
    ['unused-nan', 'add', '2 3 6 6', original.replace('  c[row * N + col]',
      '  let v99: f32 = bitcast<f32>(2143289344u);\n  c[row * N + col]'), 'nonfinite word literal'],
  ];
  for (const [name, entry, shape, shader, diagnostic] of mutations) {
    if (shader === (entry === 'add' ? original : matrix)) throw new Error('mutation did not apply');
    const shaderFile = path.join(root, `${name}.wgsl`);
    fs.writeFileSync(shaderFile, shader);
    negative(name, dest => `#check_wgsl LeanExe.WGSL.Examples.Body.${entry} ${shape} ${JSON.stringify(shaderFile)} ${JSON.stringify(dest)}`, diagnostic);
  }
  const summary = {status:'pass', sourceCases:cases.length, outputWords:cases.reduce((n,c)=>n+c.shape.rows*c.shape.cols,0),
    rejectedCases, bodyMutationPairs:2, independentMatrixProof:'pass', statementExecutionProofs:cases.length,
    evidenceDirectory:root, universalRuntimeConformanceEstablished:false};
  fs.writeFileSync(path.join(root,'summary.json'), JSON.stringify(summary,null,2)+'\n');
  console.log(JSON.stringify(summary));
} catch (error) {
  console.error(error.message);
  console.error(`Failure evidence retained at ${root}`);
  process.exitCode = 1;
}
