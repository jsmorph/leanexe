#!/usr/bin/env python3
"""Generate and check the cardinal lidar bundle through the repository Lean runner."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]


def lean(arguments, label, env, timeout='3m'):
    logs = ROOT / 'build/lidar/checks'
    logs.mkdir(parents=True, exist_ok=True)
    log = logs / (label + '.log')
    command = [str(ROOT / 'tools/leanrun'), '--timeout', timeout, *arguments]
    print(label, flush=True)
    started = time.monotonic()
    with log.open('w') as out:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=out, stderr=subprocess.STDOUT)
    with (logs/'timings.jsonl').open('a') as stream:
        stream.write(json.dumps({'check': label, 'seconds': round(time.monotonic()-started, 3),
                                 'exit_code': result.returncode})+'\n')
    content = log.read_text()
    audits = re.findall(r'depends on axioms: \[([^\]]*)\]', content)
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    unexpected = {a.strip() for audit in audits for a in audit.split(',') if a.strip()} - allowed
    if result.returncode or unexpected or ('certificate' in label and not audits):
        print(content[-9000:], file=sys.stderr)
        raise SystemExit(f'{label} failed (exit {result.returncode}, unexpected axioms {unexpected}); see {log}')
    return log


def split_certificate(path, size=8):
    source = path.read_text()
    start = source.index('def line1 :')
    finish = source.index('def lines :')
    namespace = re.search(r'namespace (Project\.Lidar\.\w+)', source).group(1)
    statements = re.split(r'(?=def line\d+ : String)', source[start:finish])
    statements = [s for s in statements if s.strip()]
    chunks = []
    for index, offset in enumerate(range(0, len(statements), size)):
        stem = f'{path.stem}Chunk{index:02d}'
        chunk = path.with_name(stem + '.lean')
        header = source[:start] if index == 0 else (
            f'import {chunks[-1].stem}\nset_option maxRecDepth 2048\nset_option maxHeartbeats 4000000\n'
            f'namespace {namespace}\nopen LeanExe.WGSL.UInt\n')
        final = min(offset+size, len(statements))
        chunk.write_text(header + ''.join(statements[offset:final]) +
                         f'\n#print axioms step{final}\nend {namespace}\n')
        chunks.append(chunk)
    path.with_suffix('.full.lean').write_text(source)
    path.write_text(f'import {chunks[-1].stem}\nset_option maxRecDepth 2048\n'
                    f'set_option maxHeartbeats 4000000\nnamespace {namespace}\n'
                    'open LeanExe.WGSL.UInt\n' + source[finish:])
    return chunks + [path]


def split_controller(path):
    source = path.read_text()
    namespace = 'Project.Lidar.ControllerArtifact'
    starts = [source.index('theorem '+name+' :') for name in ['extracted','fits','emitted','correct']]
    data = path.with_name('ControllerData.lean')
    data.write_text(source[:starts[0]] + f'\nend {namespace}\n')
    files = [data]
    for i, name in enumerate(['Extract', 'Bounds']):
        theorem = ['extracted','fits','emitted'][i]
        part = path.with_name('Controller'+name+'.lean')
        part.write_text(f'import {files[-1].stem}\nset_option maxRecDepth 4096\n'
                        f'set_option maxHeartbeats 4000000\nnamespace {namespace}\n' +
                        source[starts[i]:starts[i+1]] +
                        f'\n#print axioms {theorem}\nend {namespace}\n')
        files.append(part)
    files.extend(controller_byte_parts(path.parent))
    byteproof = path.with_name('ControllerBytes.lean')
    byteproof.write_text(f'import {files[-1].stem}\nnamespace {namespace}\n'
        'theorem emitted : LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] } = bytes := by\n'
        '  unfold LeanExe.Wasm.Binary.CoreWasm.moduleBytes LeanExe.Wasm.Binary.CoreWasm.legacyModuleBytes\n'
        '  rw [part0_eq, part1_eq, part2_eq, part3_eq, part4_eq, part10_eq]\n'
        '  unfold bytes\n'
        '  apply congrArg ByteArray.mk\n'
        '  apply Array.toList_inj.mp\n'
        '  cbv\n#print axioms emitted\n' + f'end {namespace}\n')
    files.append(byteproof)
    path.with_suffix('.full.lean').write_text(source)
    path.write_text(f'import {files[-1].stem}\nnamespace {namespace}\n' + source[starts[-1]:])
    return files + [path]


def controller_byte_parts(output):
    """Propose section/body literals from the actual WASM; Lean proves each one."""
    data = (output/'controller.wasm').read_bytes()
    def leb(offset):
        value = shift = 0
        while True:
            word = data[offset]; offset += 1
            value |= (word & 127) << shift
            if word < 128:
                return value, offset
            shift += 7
    sections = {}
    offset = 8
    while offset < len(data):
        start = offset; kind = data[offset]
        size, payload = leb(offset+1)
        offset = payload+size
        sections[kind] = (list(data[start:offset]), payload)
    count, offset = leb(sections[10][1])
    assert count == 5
    bodies = []
    for _ in range(count):
        start = offset; size, offset = leb(offset)
        offset += size
        bodies.append(list(data[start:offset]))
    expressions = [
        'typeSection { funcs := #[func] }', 'functionSection { funcs := #[func] }',
        'coreMemorySection', 'coreGlobalSection', 'exportSection { funcs := #[func] }',
        'emitFuncBody 4 func', 'coreAllocBody', 'coreResetBody', 'coreRetainBody', 'coreReleaseBody 4',
        'codeSection { funcs := #[func] }',
    ]
    values = [sections[i][0] for i in [1,3,5,6,7]] + bodies + [sections[10][0]]
    files = []
    namespace = 'Project.Lidar.ControllerArtifact'
    for i, (expression, value) in enumerate(zip(expressions, values)):
        path = output/f'ControllerPart{i:02d}.lean'
        previous = files[-1].stem if files else 'ControllerBounds'
        proof = '  cbv\n' if i < 10 else (
            '  change wasmSection 10 (vec [emitFuncBody 4 func, coreAllocBody, coreResetBody, '
            'coreRetainBody, coreReleaseBody 4]) = part10\n'
            '  rw [part5_eq, part6_eq, part7_eq, part8_eq, part9_eq]\n'
            '  rw [Project.Compiler.ContainerEncoding.vector, Project.Compiler.ContainerEncoding.section_bytes]\n'
            '  cbv\n')
        header = (f'import {previous}\nset_option cbv.maxSteps 1000000\n'
                  f'namespace {namespace}\nopen LeanExe.Wasm.Binary LeanExe.Wasm.Binary.CoreWasm\n')
        definition = f'def part{i} : List UInt8 := {value}\n'
        if i == 10:
            definition = f'def part{i} : List UInt8 := (#{value} : Array UInt8).toList\n'
            datafile = output/'ControllerCodeData.lean'
            datafile.write_text(header+definition+f'\n#check part10\nend {namespace}\n')
            files.append(datafile)
            header = header.replace(f'import {previous}', f'import {datafile.stem}')
            definition = ''
        path.write_text(header+definition+f'theorem part{i}_eq : {expression} = part{i} := by\n{proof}'
            f'#print axioms part{i}_eq\nend {namespace}\n')
        files.append(path)
    return files


def compare_artifact_bytes(output):
    for artifact in ['scan.wgsl', 'summary.wgsl', 'controller.wasm']:
        if (output/artifact).read_bytes() != (output/('certified-'+artifact)).read_bytes():
            raise SystemExit(f'{artifact} differs from the value named in its checked theorem')


def export_certified_values(output, env):
    """Serialize the values named by the checked theorems, then compare files.

    This is the explicit trusted IO boundary; it does not reconstruct shader
    headers or parse Lean source with a second hand-written representation.
    """
    source = 'import Application\n'
    for name, value, operation in [
        ('scan.wgsl', 'Project.Lidar.Artifact.shaderText', 'writeFile'),
        ('summary.wgsl', 'Project.Lidar.SummaryArtifact.shaderText', 'writeFile'),
        ('controller.wasm', 'Project.Lidar.ControllerArtifact.bytes', 'writeBinFile'),
    ]:
        target = json.dumps(str(output/('certified-'+name)))
        source += f'#eval IO.FS.{operation} {target} {value}\n'
    path = output/'Identity.lean'
    path.write_text(source)
    lean(['lake', '-d', 'proofs/talos/lean', 'env', 'lean', '-M', '8192',
          '--run', 'tools/lidar/Check.lean', str(path), str(path.with_suffix('.olean'))],
         'artifact-identity', env)
    compare_artifact_bytes(output)


def check_frontend_rejection(output, env):
    """Check that the import workaround still rejects an invalid proof."""
    source = output/'MustReject.lean'
    source.write_text('import Project.Compiler.SourceCorrectness\n'
                      'theorem invalid : (1 : Nat) = 2 := by decide\n')
    result = subprocess.run([str(ROOT/'tools/leanrun'), '--timeout', '1m',
        'lake', '-d', 'proofs/talos/lean', 'env', 'lean', '-M', '8192', '--run',
        'tools/lidar/Check.lean', str(source), str(source.with_suffix('.olean'))],
        cwd=ROOT, env=env, capture_output=True, text=True)
    log = ROOT/'build/lidar/checks/frontend-rejection.log'
    log.write_text(result.stdout+result.stderr)
    if result.returncode != 1 or 'error:' not in result.stdout or 'decide' not in result.stdout:
        raise SystemExit(f'frontend did not report the expected invalid-proof rejection; see {log}')


def finish_bundle(output, env):
    export_certified_values(output, env)
    receipt = {'schema': 1, 'milestone': 'cardinal integer lidar',
               'artifacts': {name: hashlib.sha256((output/name).read_bytes()).hexdigest()
                             for name in ['scan.wgsl','summary.wgsl','controller.wasm']},
               'assumptions': ['WebGPU implements the accepted u32 subset',
                               'host validates, copies, binds and schedules the declared buffers',
                               'WASM engine implements the modeled arithmetic semantics',
                               'file IO and the checked-source-to-external-file comparison']}
    (output/'checked.json').write_text(json.dumps(receipt,indent=2)+'\n')
    print(f'Checked bundle: {output}')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, default=ROOT / 'build/lidar/bundle')
    args = parser.parse_args()
    output = args.out.resolve()
    env = dict(os.environ)
    toolchain = ROOT / 'build/tools/lean-4.34.0-rc2-linux'
    if toolchain.exists():
        env.setdefault('LEANRUN_TOOLCHAIN', str(toolchain))
    lean(['lake', 'build', 'LeanExe.WGSL.LidarSummary', 'LeanExe.WGSL.UIntComposition'], 'compiler', env)
    lean(['lake', '-d', 'proofs/talos/lean', 'build', 'Project.Lidar.Shader',
          'Project.Lidar.Continuous', 'Project.Lidar.Controller', 'Project.Lidar.Summary',
          'Project.Compiler.ScalarResult', 'Project.Lidar.ParserChecks'], 'application', env, timeout='10m')
    lean(['lake', 'env', 'lean', '--run', 'tools/lidar/Generate.lean', str(output)], 'generate', env)
    shutil.copyfile(ROOT / 'tools/lidar/Application.lean', output / 'Application.lean')
    shutil.copyfile(ROOT / 'tools/lidar/ControllerIR.lean', output / 'ControllerIR.lean')
    shutil.copyfile(ROOT / 'tools/lidar/ControllerResult.lean', output / 'ControllerResult.lean')
    env['LEAN_PATH'] = str(output) + ':' + env.get('LEAN_PATH', '')
    check_frontend_rejection(output, env)
    for name in ['Shader', 'Summary', 'Controller', 'ControllerIR', 'ControllerResult', 'Application']:
        proof = output / (name + '.lean')
        files = (split_certificate(proof) if name in ['Shader', 'Summary'] else
                 split_controller(proof) if name == 'Controller' else [proof])
        for file in files:
            lean(['lake', '-d', 'proofs/talos/lean', 'env', 'lean', '-M', '8192',
                  '--run', 'tools/lidar/Check.lean', str(file), str(file.with_suffix('.olean'))],
                 file.stem.lower() + ('-definitions' if file.stem.endswith('Data') else '-certificate'), env)
    finish_bundle(output, env)


if __name__ == '__main__':
    main()
