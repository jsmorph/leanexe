#!/usr/bin/env python3
"""Bundle and independently check the general arithmetic compiler proof."""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parent.parent
TARGET = 'Project.Compiler.ArithmeticCompilerAudit'
TOOLCHAIN = 'leanprover/lean4:v4.34.0-rc2'
TALOS = '87e3aa5e8f6e6f3b3eb5e7e4c5aba43071002d47'
PINS = {
    'mathlib': '85e3a25e006c35636f0e53b0e9296caca2685bc0',
    'batteries': 'd54dddc581e08be364c278052863524bff7a99a9',
    'Qq': '507746ab8f4b643ccdacb2ec4cdb5853fa9f8ab3',
    'plausible': 'd9598f07b1bc701f1e3aae163d2681c1fd978793',
    'LeanSearchClient': 'ba67e212be1197b84c1f1f6299488a10a3002713',
    'importGraph': 'd8823026ac7ef130c253089d95685f9877b95323',
    'proofwidgets': 'a8acbfd87375ff4abe14ce09db5b7664d383bc7f',
    'aesop': '18889deb9e83ea7420ef51c160d6f88552e744e3',
    'Cli': 'ab3a82db9fea14cf0fd7f5a2de650f4b534640af',
}
URLS = {
    'mathlib': 'https://github.com/leanprover-community/mathlib4',
    'batteries': 'https://github.com/leanprover-community/batteries',
    'Qq': 'https://github.com/leanprover-community/quote4',
    'plausible': 'https://github.com/leanprover-community/plausible',
    'LeanSearchClient': 'https://github.com/leanprover-community/LeanSearchClient',
    'importGraph': 'https://github.com/leanprover-community/import-graph',
    'proofwidgets': 'https://github.com/leanprover-community/ProofWidgets4',
    'aesop': 'https://github.com/leanprover-community/aesop',
    'Cli': 'https://github.com/leanprover/lean4-cli',
}


def digest(file):
    return hashlib.sha256(file.read_bytes()).hexdigest()


def git(directory, *args):
    return subprocess.check_output(['git', '-C', str(directory), *args], text=True).strip()


def write_json(file, value):
    file.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def imports(file):
    """Read Lean's module header, including nested comments and public imports."""
    source = file.read_text()
    clean = []
    i, depth = 0, 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            clean.append('  ')
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            clean.append('  ')
            i += 2
        elif depth:
            clean.append('\n' if source[i] == '\n' else ' ')
            i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            clean.append(source[i])
            i += 1
    if depth:
        raise ValueError(f'unclosed comment in {file}')
    result = []
    for line in ''.join(clean).splitlines():
        line = line.strip()
        if not line or line in ('module', 'prelude'):
            continue
        match = re.fullmatch(r'(?:public\s+)?import\s+(.+)', line)
        if not match:
            break
        modules = match[1].split()
        if not all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*', x)
                   for x in modules):
            raise ValueError(f'unsupported import syntax in {file}: {line}')
        result.extend(modules)
    return result


def closure(roots):
    pending, sources, external = [TARGET], {}, set()
    while pending:
        name = pending.pop()
        if name in sources or name in external:
            continue
        prefix = name.split('.')[0]
        if prefix in ('Init', 'Lean', 'Mathlib'):
            external.add(name)
            continue
        if prefix not in roots:
            raise ValueError(f'unresolved dependency: {name}')
        file = roots[prefix] / (name.replace('.', '/') + '.lean')
        if not file.is_file():
            raise ValueError(f'missing source: {file}')
        sources[name] = file
        pending.extend(imports(file))
    return sources, sorted(external)


def check_pins(manifest):
    packages = manifest['packages']
    if len(packages) != len(PINS) or {p['name'] for p in packages} != PINS.keys():
        raise ValueError('unexpected dependency set')
    if manifest.get('name') != 'ArithmeticCompilerProof' or manifest.get('packagesDir') != '.lake/packages':
        raise ValueError('unexpected Lake package identity or directory')
    for p in packages:
        name = p['name']
        if (p['type'] != 'git' or p['rev'] != PINS[name] or p['url'] != URLS[name]
                or p.get('subDir') is not None or 'dir' in p):
            raise ValueError(f'unexpected dependency pin or path: {name}')


def create(directory, archive):
    proof = ROOT / 'proofs/talos/lean'
    upstream = proof / '.lake/packages/CodeLib'
    if git(upstream, 'rev-parse', 'HEAD') != TALOS:
        raise ValueError('Interpreter checkout does not match pinned Talos revision')
    sources, external = closure({'LeanExe': ROOT, 'Project': proof,
                                 'Interpreter': upstream / 'interpreter'})
    manifest = json.loads((proof / 'lake-manifest.json').read_text())
    manifest['name'] = 'ArithmeticCompilerProof'
    manifest['packages'] = [p for p in manifest['packages']
                            if p['type'] == 'git' and p['name'] not in ('CodeLib', 'iris')]
    for package in manifest['packages']:
        package['inherited'] = package['name'] != 'mathlib'
        package['inputRev'] = package['rev']
    check_pins(manifest)
    if (ROOT / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise ValueError('unexpected Lean toolchain')
    directory.mkdir(parents=True, exist_ok=False)
    for name, source in sources.items():
        destination = directory / (name.replace('.', '/') + '.lean')
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, destination)
    for name in ('lean-toolchain', 'tools/leanrun', 'tools/leanrun-macos.c',
                 'tools/arithmetic-package.py', 'tools/arithmetic-audit.py'):
        destination = directory / name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(ROOT / name, destination)
    shutil.copy2(upstream / 'LICENSE', directory / 'INTERPRETER-LICENSE')
    (directory / 'NOTICE').write_text(
        f'Interpreter sources are from https://github.com/jsmorph/talos at {TALOS}.\n'
        'See INTERPRETER-LICENSE for their license. LeanExe and Project sources\n'
        'are from https://github.com/jsmorph/leanexe at the commit in proof-package.json.\n')
    if (ROOT / 'LICENSE').exists():
        shutil.copy2(ROOT / 'LICENSE', directory / 'LICENSE')
    (directory / 'lakefile.toml').write_text(f'''name = "ArithmeticCompilerProof"
version = "0.1.0"
[[require]]
name = "mathlib"
scope = "leanprover-community"
git = "{URLS['mathlib']}"
rev = "{PINS['mathlib']}"
[[lean_lib]]
name = "LeanExe"
[[lean_lib]]
name = "Interpreter"
[[lean_lib]]
name = "Project"
''')
    write_json(directory / 'lake-manifest.json', manifest)
    (directory / 'README.md').write_text(f'''# General arithmetic compiler proof

This source package proves `{TARGET}` and its imported theorems for every
successfully admitted arithmetic declaration, using the production compiler
and byte emitter definitions. It contains no generated per-program theorem.

Install Python 3, Git and `{TOOLCHAIN}`. On macOS, a C compiler is also needed
by the runner. Set LEANRUN_TOOLCHAIN to the pinned installation if needed.
Where local execution is authorized, set LEANRUN_LOCAL=1; the runner retains
its shared lock, one Lean thread, and timeout. Otherwise it uses systemd limits.
On this project's authorized Mac, LEANRUN_INHERIT_PRIORITY=1 is also used.

From this directory, run:

```sh
python3 tools/arithmetic-package.py verify .
```

The verifier checks all bundled hashes and exact pins, requires no existing
package build, and invokes `tools/leanrun --timeout 900 lake build {TARGET}`.
Lake may fetch the pinned third-party dependencies. To reuse existing pinned
third-party sources and caches, add `--dependencies /absolute/dependency/directory`.
Only the nine listed third-party packages are linked; original LeanExe, Project,
and Interpreter build products are never imported. No compiler CLI or generator
runs. All bundled Lean modules are rebuilt by the package's own Lake project.
Output and all nine theorem dependency audits are in verification.log and
verification-result.json. The runtime validator theorems allow only propext;
other audited compiler theorems allow propext, Classical.choice and Quot.sound.

The proof covers the restricted UInt64 arithmetic source grammar, exact output
bytes, decoding, validation, export lookup and terminating invocation in the
pinned interpreter. It does not prove CLI IO, all Lean evaluation, or agreement
of every external engine with that interpreter. The source supports UInt64
arguments/literals and nested add/sub/mul/unsigned division/remainder/bitwise
operations/masked shifts, UInt64 let bindings and conditionals over canonical
UInt64 comparisons, standard pure Id operations and local scalar functions,
subject to explicit format-size bounds. Function shapes include unary UInt64
functions and Unit-prefixed scalar continuations. One ascending unit-step
[:count.toNat] range loop with a UInt64 accumulator and yielding steps is
supported, including explicit UInt64.ofNat conversion of its Nat index, local
function bindings, standard Id monadic UInt64 bindings, supported scalar branch
continuations and continue in the step.
Top-level helpers, breaks, multiple/nested loops, custom instances and heap
values are excluded.

The JSON inventory detects accidental content changes; it is not a signature.
Check this archive's SHA-256 against the separately published evidence to
establish its identity. Third-party dependencies remain part of the trust base.
''')
    files = {p.relative_to(directory).as_posix(): digest(p)
             for p in sorted(directory.rglob('*')) if p.is_file()}
    inventory = {'schema': 1, 'target': TARGET, 'toolchain': TOOLCHAIN,
                 'dependencies': PINS, 'interpreterRevision': TALOS,
                 'commit': git(ROOT, 'rev-parse', 'HEAD'),
                 'tree': git(ROOT, 'rev-parse', 'HEAD^{tree}'),
                 'sources': sorted(sources), 'externalImports': external, 'files': files}
    write_json(directory / 'proof-package.json', inventory)
    check(directory)
    archive.parent.mkdir(parents=True, exist_ok=True)
    if archive.exists():
        raise ValueError(f'archive already exists: {archive}')
    with tarfile.open(archive, 'w:gz') as tar:
        for name in sorted([*files, 'proof-package.json']):
            tar.add(directory / name, arcname='arithmetic-proof/' + name, recursive=False)
    print(f'Bundled {len(sources)} Lean source modules; archive SHA-256 {digest(archive)}')
    print(archive)


def check(directory):
    inventory = json.loads((directory / 'proof-package.json').read_text())
    if (inventory.get('schema') != 1 or inventory.get('target') != TARGET
            or inventory.get('toolchain') != TOOLCHAIN or inventory.get('dependencies') != PINS
            or inventory.get('interpreterRevision') != TALOS):
        raise ValueError('unknown proof schema, target, toolchain or dependency pins')
    files = inventory['files']
    for name, expected in files.items():
        file = directory / name
        if (Path(name).is_absolute() or '..' in Path(name).parts or file.is_symlink()
                or directory not in file.resolve().parents or not file.is_file()):
            raise ValueError(f'invalid or missing bundled path: {name}')
        if digest(file) != expected:
            raise ValueError(f'content hash mismatch: {name}')
    allowed_outputs = {'proof-package.json', 'verification.log', 'verification-result.json'}
    for file in directory.rglob('*'):
        relative = file.relative_to(directory)
        if relative.parts[0] == '.lake':
            continue
        if file.is_symlink():
            raise ValueError(f'unexpected symlink: {relative}')
        if file.is_file() and relative.as_posix() not in files and relative.as_posix() not in allowed_outputs:
            raise ValueError(f'uninventoried input: {relative}')
    required = {'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'tools/leanrun',
                'tools/leanrun-macos.c', 'tools/arithmetic-package.py', 'tools/arithmetic-audit.py',
                'README.md', 'NOTICE', 'INTERPRETER-LICENSE'}
    if not required <= files.keys():
        raise ValueError('incomplete package inventory')
    if (directory / 'lean-toolchain').read_text().strip() != TOOLCHAIN:
        raise ValueError('Lean toolchain mismatch')
    check_pins(json.loads((directory / 'lake-manifest.json').read_text()))
    sources, external = closure({name: directory for name in ('LeanExe', 'Project', 'Interpreter')})
    if sorted(sources) != inventory['sources'] or external != inventory['externalImports']:
        raise ValueError('source dependency closure mismatch')
    if {name.replace('.', '/') + '.lean' for name in sources} != {p for p in files if p.endswith('.lean')}:
        raise ValueError('source inventory does not equal proof dependency closure')
    print(f'Checked package integrity and {len(sources)} source modules.', flush=True)
    return inventory


def verify(directory, dependencies):
    inventory = check(directory)
    if (directory / '.lake/build').exists():
        raise ValueError('package already has .lake/build; verify a new archive extraction')
    packages = directory / '.lake/packages'
    if dependencies:
        packages.mkdir(parents=True, exist_ok=True)
        for name, revision in PINS.items():
            source = (dependencies / name).resolve()
            if git(source, 'rev-parse', 'HEAD') != revision:
                raise ValueError(f'third-party checkout pin mismatch: {name}')
            destination = packages / name
            if destination.exists() or destination.is_symlink():
                raise ValueError(f'dependency already exists: {destination}')
            destination.symlink_to(source, target_is_directory=True)
    env = os.environ.copy()
    for name in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LAKE', 'LAKE_HOME', 'LAKE_PACKAGES_DIR'):
        env.pop(name, None)
    # Keep package configuration/cache local; never inherit another project's runner cache.
    env.pop('LEANRUN_CACHE_HOME', None)
    command = ['tools/leanrun', '--timeout', '900', 'lake', 'build', TARGET]
    with (directory / 'verification.log').open('w') as log:
        completed = subprocess.run(command, cwd=directory, env=env, stdout=log, stderr=subprocess.STDOUT)
    if completed.returncode:
        raise ValueError(f'proof build exited {completed.returncode}; see {directory / "verification.log"}')
    spec = importlib.util.spec_from_file_location('arithmetic_audit', directory / 'tools/arithmetic-audit.py')
    auditor = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(auditor)
    audits = auditor.audit((directory / 'verification.log').read_text())
    write_json(directory / 'verification-result.json', {
        'commit': inventory['commit'], 'tree': inventory['tree'], 'command': command,
        'exitStatus': completed.returncode, 'sourceModules': len(inventory['sources']),
        'audits': audits, 'logSha256': digest(directory / 'verification.log'),
        'localMode': env.get('LEANRUN_LOCAL', '0'), 'toolchain': TOOLCHAIN,
    })
    print('Standalone arithmetic compiler proof verified.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='mode', required=True)
    create_parser = sub.add_parser('create')
    create_parser.add_argument('directory', type=Path)
    create_parser.add_argument('archive', type=Path)
    for mode in ('check', 'verify'):
        p = sub.add_parser(mode)
        p.add_argument('directory', type=Path)
        if mode == 'verify':
            p.add_argument('--dependencies', type=Path)
    args = parser.parse_args()
    directory = args.directory.resolve()
    if args.mode == 'create':
        create(directory, args.archive.resolve())
    elif args.mode == 'check':
        check(directory)
    else:
        verify(directory, args.dependencies.resolve() if args.dependencies else None)


if __name__ == '__main__':
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        sys.exit(str(error))
