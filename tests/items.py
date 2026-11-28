"""The items of leanexe's check, which tools/check runs.

An item is one command run in the root of a copy of the built tree, with its memory in GiB and its
CPUs, the tools it needs, the items whose outputs it reads, the files whose hashes decide whether a
recorded pass still holds, and the files it writes that later items or the status read.  Each item
belongs to a step, a row of STATUS.md, which is one of the steps of the former tools/full-check, and
counts() gives a step's counts from the logs of its items, as tools/full-check gave them from the
step's log.  The commands and their pass criteria are the drivers' own: an item runs a driver, a
driver's part, or a driver on some of its modules.

The memory of an item is the peak that the full check of 2026-11-27 measured for its step, with a
margin.  tools/check sets LEANRUN_MEMORY_HIGH to 2G less, and at least 4G, for the Lean commands
whose drivers name no limit of their own.
"""

import os
import re
import subprocess

# The tests of the tools, run by bash in the tree with the host's environment.  The tree's own
# programs are tested in the tree, since a copy can lack one.
TOOLS = {
    'lean': 'test -x "${ELAN_HOME:-$HOME/.elan}/toolchains/$(sed "s,/,--,g; s,:,---,g" lean-toolchain)/bin/lean"',
    'aarch64': 'test "$(uname -sm)" = "Linux aarch64"',
    'git': 'git rev-parse --git-dir',
    'ccomp': 'command -v "${CCOMP:-ccomp}"',
    'clightgen': 'command -v "${CLIGHTGEN:-clightgen}"',
    'qemu': 'command -v "${QEMU:-qemu-system-aarch64}"',
    'qemu-arm': 'command -v qemu-system-arm',
    'qemu-user': 'v=$("${QEMU_USER:-/usr/bin/qemu-aarch64}" --version | sed -n "1s/.* version \\([0-9]*\\)\\.\\([0-9]*\\).*/\\1 \\2/p"); set -- $v; [ "$#" -eq 2 ] && { [ "$1" -gt 9 ] || { [ "$1" -eq 9 ] && [ "$2" -ge 2 ]; }; }',
    'nm': 'command -v "${NM:-nm}"',
    'dtc': 'command -v "${DTC:-dtc}"',
    'cc': 'command -v "${CC:-cc}"',
    'coqc': 'command -v coqc',
    'compcert': 'test -f "$COMPCERT_TREE/_CoqProject" && test -f "$COMPCERT_TREE/driver/Compiler.vo"',
    'compcert-clight': 'test -f "$COMPCERT_TREE/cfrontend/ClightBigstep.vo" && test -f "$COMPCERT_TREE/export/Clightdefs.vo" && test -x "$COMPCERT_TREE/clightgen"',
    'compcert-aarch64': 'test "$(sed -n "s/^ARCH=//p" "$COMPCERT_TREE/Makefile.config")" = aarch64',
    'uv': 'command -v uv',
    'python3': 'command -v python3',
    'node': 'command -v node',
    'wasm-tools': 'command -v wasm-tools',
    'strace': 'command -v strace',
    'time': 'test -x /usr/bin/time',
    'sha256sum': 'command -v sha256sum',
    'systemd-run': 'command -v systemd-run',
    'wasmtime-host': 'test -x build/tools/leanexe-wasmtime-host && ! test tools/wasmtime-host.c -nt build/tools/leanexe-wasmtime-host',
    'vulkan': 'test -e /usr/lib/chromium/vk_swiftshader_icd.json && test -e /usr/share/vulkan/icd.d/lvp_icd.json && test -e build/tools/leanexe-webgpu-host',
    'cuda': 'test -x "${CUDA_HOME:-/usr/local/cuda}/bin/ptxas" && test -x build/tools/leanexe-cuda-host && build/tools/leanexe-cuda-host info',
    'testsuite': 'test "$(git -C .lake/packages/WasmInterpreterLean submodule status vendor/testsuite | cut -c1)" = " "',
}

# The steps in the order of STATUS.md, with their titles.
STEPS = [
    ('build', '`lake build` of every library and the test executables'),
    ('axioms', '`tests/verified/AllAxioms.lean`'),
    ('verified', '`tests/verified/run.sh`'),
    ('drone', '`tests/drone/run.sh`'),
    ('chunks', '`tests/modules/chunks.py`'),
    ('native-verified', '`tests/native/verified.sh`'),
    ('native-verified-aligned', '`tests/native/verified.sh --aligned`'),
    ('native-aligned', '`tests/native/aligned.sh`'),
    ('native-run', '`tests/native/run.sh`'),
    ('native-bytes', '`tests/native/bytes.sh`'),
    ('native-clight', '`tests/native/clight.sh 7 300 aarch64`'),
    ('wasi', '`tests/wasi/run.sh`'),
    ('wasi-sys', '`tests/wasi/sys-run.sh`'),
    ('random-histogram', '`tests/random-histogram/run.sh`'),
    ('random-choice', '`tests/random-choice/run.sh`'),
    ('manifest-check', '`tests/manifest-check/run.sh`'),
    ('linux-sys', '`tests/linux/sys-run.sh`'),
    ('a64-elf', '`tests/linux/a64-elf.sh`'),
    ('a64-wasi', '`tests/linux/a64-wasi.sh`'),
    ('a64-wasi-clocks', '`tests/linux/a64-wasi-clocks.sh`'),
    ('a64-wasi-preopen', '`tests/linux/a64-wasi-preopen.sh`'),
    ('a64-wasi-files', '`tests/linux/a64-wasi-files.sh`'),
    ('baremetal-run', '`tests/baremetal/run.sh`'),
    ('baremetal-programs', '`tests/baremetal/programs.sh`'),
    ('baremetal-inputs', '`tests/baremetal/inputs.sh`'),
    ('baremetal-ctl', '`tests/baremetal/ctl.sh`'),
    ('baremetal-verified', '`tests/baremetal/verified.sh`'),
    ('a64-images', '`tests/baremetal/a64-images.sh`'),
    ('a64-uart', '`tests/baremetal/a64-uart.sh`'),
    ('bms-board', '`tests/baremetal/m7-board.sh check bms`'),
    ('bms-qemu', '`tests/baremetal/m7-qemu.sh bms`'),
    ('bignum', '`tests/bignum/run.sh`'),
    ('bignum-native', '`tests/bignum/native.sh`'),
    ('bignum-calc-bare', '`tests/bignum-calc/bare.sh`'),
    ('bignum-calc-image', '`tests/bignum-calc/image.sh --check`'),
    ('isla', '`tests/isla/theorems.sh`'),
    ('m7-isla', '`tests/isla/m7-theorems.sh`'),
    ('vkb', '`VKB/Check.lean`'),
    ('rocq', '`rocq/check.sh`'),
    ('clight-rocq', '`tests/native/clight-rocq.sh` on the programs of `tests/native/clight.sh 7 300 aarch64`'),
    ('clightn', '`clightn/check.sh --mutations`'),
    ('wgsl-verified-emit', '`tests/wgsl/run.sh --verified --emit-only`'),
    ('wgsl-verified-drivers', '`tests/wgsl/run.sh --verified --drivers-only`'),
    ('wgsl-default-emit', '`tests/wgsl/run.sh --emit-only`'),
    ('wgsl-default-drivers', '`tests/wgsl/run.sh --drivers-only`'),
    ('gpt32', '`tests/gpt32/native.sh`'),
    ('ptx', '`tests/ptx/run.sh`'),
    ('talos', '`tests/talos/run.sh`'),
    ('references', 'checks against independent references'),
    ('layout', '`tools/source-layout` and `tools/check-doc-links.mjs`'),
]

# The checks that no item runs, with the reason.
UNRUN = [
    ('the file theorem modules `tests/TestSupport/A64/ImageFilesRcv.lean` and `ImageFilesRcvMaine.lean`',
     'they need the RCV corpus, which no machine of the check holds'),
]

LIBRARIES = ['LeanExe', 'Examples', 'Demos', 'Verified', 'Library', 'TestSupport']
WORK = 'build/check/work'


def item(id, step, cmd, mem=4, cpus=1, tools=(), deps=(), inputs=(), outputs=(), exclusive=(),
         timeout=7200, env=None, primary=False, scripts=(), targets=(), portable=False, peak=None):
    """An item.  cmd is a bash command; targets are Lake targets it reads, and scripts are the files
    whose text names the Lake executables it runs, which the build also includes.  An item runs on
    an AArch64 machine, where the tree's executables were built, unless it is portable: it then
    reads only modules, which Lean reads on any machine.  peak is the expected peak memory in GiB,
    which a machine's peak_max compares with the larger of it and the recorded peak."""
    return {
        'peak': peak,
        'targets': list(targets),
        'id': id, 'step': step, 'cmd': cmd, 'mem': mem, 'cpus': cpus,
        'tools': sorted(set(tools) | {'lean'} | (set() if portable else {'aarch64'})), 'deps': list(deps), 'inputs': list(inputs),
        'outputs': list(outputs), 'exclusive': list(exclusive), 'timeout': timeout,
        'env': env or {}, 'primary': primary, 'scripts': list(scripts),
    }


def registry(root, name):
    with open(os.path.join(root, name)) as f:
        return [line.rstrip('\n') for line in f if line.strip() and not line.startswith('#')]


def chunks(xs, n):
    """xs in n groups, the i-th element in group i mod n, so that neighbors spread."""
    n = max(1, min(n, len(xs)))
    return [xs[i::n] for i in range(n)]


def batches(xs, size):
    return [xs[i:i + size] for i in range(0, len(xs), size)]


def items(root):
    out = []
    add = out.append
    native = ['ccomp', 'clightgen', 'aarch64']
    hosted = ['wasm-tools', 'wasmtime-host', 'aarch64']
    # The tracked files but the Markdown files, which only the layout items read; 'docs' adds them.
    tree = ['tree']

    add(item('axioms', 'axioms', 'tools/leanrun --timeout 1h lake env lean --run tests/verified/AllAxioms.lean',
             mem=16, inputs=tree))

    # tests/verified/run.sh, by its parts.
    parts = subprocess.run(['tests/verified/run.sh', '--parts'], cwd=root, check=True,
                           capture_output=True, text=True).stdout.split()
    modules = [line.split(':')[2] for line in registry(root, 'tests/verified/modules.txt')]
    emit_of = {}
    emits = [p[5:] for p in parts if p.startswith('emit:')]
    vcmd = 'tests/verified/run.sh --no-cache'
    vtools = hosted
    vin = ['tests/verified', 'tests/gpt', 'tests/modules', 'tests/slew'] + tree
    for i, group in enumerate(batches(emits, 16)):
        id = f'verified/emit-{i + 1:02d}'
        for name in group:
            emit_of[name] = id
        add(item(id, 'verified', vcmd + ''.join(f' --part emit:{n}' for n in group), mem=8, cpus=1,
                 tools=vtools, inputs=vin, outputs=[f'build/verified/{n}.wasm' for n in group],
                 scripts=['tests/verified/run.sh']))

    # The emissions peak at 5.6 GB; the other parts, of which one reached 7.5 GB in the serial
    # check, take 10.
    def vitem(id, ps, names, mem=10, timeout=7200, portable=False, peak=None):
        deps = sorted({emit_of[n] for n in names})
        add(item(id, 'verified', vcmd + ''.join(f' --part {p}' for p in ps), mem=mem, cpus=1,
                 tools=[] if portable else vtools, deps=deps, inputs=vin, timeout=timeout,
                 scripts=['tests/verified/run.sh'], portable=portable, peak=peak))

    vitem('verified/gpt', ['gpt'], ['gpt'])
    vitem('verified/module-cases-euler', ['module-cases:euler'], ['euler'])
    vitem('verified/module-cases-shapes', ['module-cases:shapes'], ['sums'])
    vitem('verified/slew-edges', ['slew-edges'], ['slew'])
    files = [p for p in parts if p.startswith('file:')]
    # The file theorems, audits, and accuracy checks read only modules and written files, so they run
    # on any processor.
    for i, group in enumerate(batches(files, 8)):
        vitem(f'verified/file-{i + 1:02d}', group, [p[5:] for p in group], mem=9, portable=True, peak=4)
    cases = [p for p in parts if p.startswith('cases:')]
    for i, group in enumerate(chunks(cases, 12)):
        vitem(f'verified/cases-{i + 1:02d}', group, [p[6:] for p in group])
    vitem('verified/cases-complete', ['cases-complete'], [])
    audits = [p for p in parts if p.startswith('audit:')]
    for i, group in enumerate(batches(audits, 4)):
        vitem(f'verified/audit-{i + 1:02d}', group, [], mem=9, portable=True, peak=4)
    for p in parts:
        if p.startswith('accuracy:'):
            name = os.path.basename(p).removesuffix('.lean')
            vitem(f'verified/accuracy-{name}', [p], [], mem=9, portable=True, peak=6)

    add(item('drone', 'drone', 'tests/drone/run.sh', mem=2, tools=['wasmtime-host', 'aarch64'],
             deps=[emit_of['drone']], inputs=['tests/drone'] + tree))
    add(item('chunks', 'chunks', 'uv run tests/modules/chunks.py', mem=2, tools=['uv', 'aarch64'],
             deps=[emit_of['insert']], inputs=['tests/modules'] + tree))

    for key, flags in [('native-verified', ''), ('native-verified-aligned', ' --aligned')]:
        add(item(key, key, 'tests/native/verified.sh' + flags, mem=8, tools=native,
                 exclusive=['build/native/verified'], inputs=['tests/native'] + tree,
                 scripts=['tests/native/verified.sh']))
    add(item('native-aligned', 'native-aligned', 'tests/native/aligned.sh', mem=5, tools=native,
             inputs=tree, scripts=['tests/native/aligned.sh']))
    add(item('native-run', 'native-run', 'tests/native/run.sh', mem=2, tools=native, inputs=tree,
             scripts=['tests/native/run.sh']))
    add(item('native-bytes', 'native-bytes', 'tests/native/bytes.sh', mem=2, tools=native, inputs=tree,
             scripts=['tests/native/bytes.sh']))
    add(item('native-clight', 'native-clight', 'tests/native/clight.sh 7 300 aarch64', mem=2,
             tools=['ccomp', 'aarch64'], inputs=tree, outputs=['build/native/clight/7'],
             scripts=['tests/native/clight.sh']))

    add(item('wasi', 'wasi', 'tests/wasi/run.sh', mem=9, tools=hosted, inputs=tree,
             scripts=['tests/wasi/run.sh']))
    add(item('wasi-sys', 'wasi-sys', 'tests/wasi/sys-run.sh', mem=2, tools=hosted, inputs=tree,
             scripts=['tests/wasi/sys-run.sh']))
    demo_tools = hosted + ['strace', 'qemu-user']
    for name, mem, extra in [('random-histogram', 4, []), ('random-choice', 7, ['time']),
                             ('manifest-check', 7, ['sha256sum'])]:
        add(item(name, name, f"RUNNERS='wasm native qemu' tests/{name}/run.sh", mem=mem,
                 tools=demo_tools + extra, inputs=tree, scripts=[f'tests/{name}/run.sh']))

    add(item('linux-sys', 'linux-sys', 'tests/linux/sys-run.sh', mem=2,
             tools=['aarch64', 'cc', 'qemu-user', 'uv', 'systemd-run'], inputs=tree))
    for name, mem, extra in [
            ('a64-elf', 9, ['systemd-run']),
            ('a64-wasi', 20, ['strace', 'uv', 'systemd-run', 'wasmtime-host']),
            ('a64-wasi-clocks', 4, ['wasm-tools', 'strace', 'uv', 'systemd-run', 'wasmtime-host']),
            ('a64-wasi-preopen', 14, ['wasm-tools', 'strace', 'wasmtime-host']),
            ('a64-wasi-files', 12, ['wasm-tools', 'strace', 'uv', 'wasmtime-host'])]:
        add(item(name, name, f'tests/linux/{name}.sh', mem=mem,
                 tools=['aarch64', 'qemu-user'] + extra, inputs=tree, scripts=[f'tests/linux/{name}.sh']))

    bm = ['ccomp', 'qemu', 'aarch64']
    add(item('baremetal-run', 'baremetal-run', 'ACCEL=tcg tests/baremetal/run.sh', mem=2,
             tools=bm + ['nm', 'dtc'], inputs=tree))
    for name in ['programs', 'inputs', 'ctl']:
        add(item(f'baremetal-{name}', f'baremetal-{name}', f'ACCEL=tcg tests/baremetal/{name}.sh',
                 mem=2, tools=bm + ['clightgen'], inputs=tree, scripts=[f'tests/baremetal/{name}.sh']))
    translated = modules
    # A group runs JOBS QEMU processes at once, each a little above one CPU, so three of them take
    # four CPUs.
    for i, group in enumerate(chunks(translated, 24)):
        id = f'baremetal-verified/{i + 1:02d}'
        add(item(id, 'baremetal-verified',
                 f'JOBS=3 tests/baremetal/verified.sh --out {WORK}/{id}' +
                 ''.join(f' --module {n}' for n in group),
                 mem=6, cpus=4, tools=bm, inputs=tree, scripts=['tests/baremetal/verified.sh']))
    add(item('a64-images', 'a64-images', 'ACCEL=tcg tests/baremetal/a64-images.sh', mem=20, cpus=2,
             tools=['qemu', 'aarch64'], inputs=tree, scripts=['tests/baremetal/a64-images.sh']))
    add(item('a64-uart', 'a64-uart', 'ACCEL=tcg tests/baremetal/a64-uart.sh', mem=7,
             tools=['qemu', 'aarch64'], inputs=tree, scripts=['tests/baremetal/a64-uart.sh']))

    # The file theorems of the BMS step's images, tests/TestSupport/M7/BmsBoardFile.lean without the
    # board, and BmsQemuFile.lean with the run under QEMU's mps2-an500.
    add(item('bms-board', 'bms-board', 'tests/baremetal/m7-board.sh check bms', mem=27, cpus=2, inputs=tree,
             timeout=4 * 3600, scripts=['tests/baremetal/m7-board.sh']))
    add(item('bms-qemu', 'bms-qemu', 'tests/baremetal/m7-qemu.sh bms', mem=27, cpus=2, tools=['qemu-arm', 'uv'],
             inputs=tree, timeout=4 * 3600, scripts=['tests/baremetal/m7-qemu.sh']))

    # The bignum library's three modules against Node's BigInt and native Lean, their C forms on the
    # cases that run.sh writes, and the calculator's bare-metal program and Image.
    add(item('bignum/run', 'bignum', 'tests/bignum/run.sh', mem=12, cpus=2, tools=['node', 'wasm-tools'],
             inputs=tree, outputs=['build/bignum'], timeout=4 * 3600,
             targets=['Library.Numerics.Bignum.Call', 'Library.Numerics.Bignum.Second.Call',
                      'Library.Numerics.Bignum.Third.Call', 'TestSupport.Bignum.Cases']))
    add(item('bignum/native', 'bignum-native', 'tests/bignum/native.sh', mem=10, cpus=2,
             tools=['ccomp', 'clightgen'], deps=['bignum/run'], inputs=tree, timeout=4 * 3600,
             targets=['Library.Numerics.Bignum.NativeRuntime', 'Library.Numerics.Bignum.Second.NativeRuntime',
                      'Library.Numerics.Bignum.Third.NativeRuntime']))
    add(item('bignum-calc/bare', 'bignum-calc-bare', 'ACCEL=tcg tests/bignum-calc/bare.sh', mem=8, cpus=2,
             tools=['ccomp', 'clightgen', 'qemu', 'node'], inputs=tree, timeout=4 * 3600,
             targets=['Demos.BignumCalc.Bare']))
    # The Image's kernel check peaks at 24.9 GiB under the script's MemoryHigh of 28G.
    add(item('bignum-calc/image', 'bignum-calc-image', 'ACCEL=tcg tests/bignum-calc/image.sh --check', mem=31,
             cpus=2, tools=['qemu', 'node'], inputs=tree, timeout=4 * 3600, targets=['Demos.BignumCalc.BytesBare']))

    # The Isla theorems, a module to an item.  An elaboration keeps one or two threads busy (the
    # longest A64 modules one), so each takes two.  The largest A64 process reaches about 8 GB.
    for f in sorted(os.listdir(os.path.join(root, 'tests/TestSupport/A64/Isla'))):
        if f.endswith('.lean'):
            m = f.removesuffix('.lean')
            cpus = 2
            add(item(f'isla/{m}', 'isla', f'ISLA_CPUS={cpus} tests/isla/theorems.sh {m}', mem=9,
                     cpus=cpus, timeout=4 * 3600, portable=True, peak=8.5,
                     inputs=['tests/isla/theorems.sh', f'lean:tests/TestSupport/A64/Isla/{f}', 'tests/isla']))
    for f in sorted(os.listdir(os.path.join(root, 'tests/TestSupport/M7/Isla'))):
        if f.endswith('.lean'):
            m = f.removesuffix('.lean')
            add(item(f'm7-isla/{m}', 'm7-isla', f'ISLA_CPUS=2 tests/isla/m7-theorems.sh {m}', mem=6,
                     cpus=2, tools=['time'], timeout=4 * 3600, portable=True,
                     inputs=['tests/isla/m7-theorems.sh', f'lean:tests/TestSupport/M7/Isla/{f}', 'tests/isla']))

    # The VKB check reads the history of the entries with Git, which only the primary's tree has.
    add(item('vkb', 'vkb', 'tools/leanrun --timeout 10m lake env lean --run VKB/Check.lean VKB/entries',
             mem=13, inputs=['VKB'] + tree, primary=True))
    add(item('rocq', 'rocq', 'rocq/check.sh "$COMPCERT_TREE"', mem=6, tools=['coqc', 'compcert'],
             inputs=['rocq']))
    # clight-rocq.sh runs JOBS files at once, all the machine's processors unless set.
    add(item('clight-rocq', 'clight-rocq', 'tests/native/clight-rocq.sh build/native/clight/7 "$COMPCERT_TREE"',
             mem=6, cpus=4, env={'JOBS': '4'}, tools=['coqc', 'compcert-clight'], deps=['native-clight'],
             inputs=tree))
    add(item('clightn', 'clightn', 'clightn/check.sh --mutations "$COMPCERT_TREE"', mem=19, cpus=2,
             tools=['coqc', 'uv', 'compcert', 'compcert-aarch64'], inputs=tree, timeout=3 * 3600))

    for mode, flag in [('verified', '--verified '), ('default', '')]:
        d = f'{WORK}/wgsl-{mode}'
        add(item(f'wgsl-{mode}-emit', f'wgsl-{mode}-emit', f'rm -rf {d} && tests/wgsl/run.sh {flag}--emit-only {d}',
                 mem=8, inputs=tree, outputs=[d]))
        add(item(f'wgsl-{mode}-drivers', f'wgsl-{mode}-drivers', f'tests/wgsl/run.sh {flag}--drivers-only {d}',
                 mem=3, tools=['vulkan', 'aarch64'], deps=[f'wgsl-{mode}-emit'], inputs=tree))
    add(item('gpt32', 'gpt32', f'tests/gpt32/native.sh {WORK}/gpt32', mem=6,
             tools=['vulkan', 'wasm-tools', 'node', 'aarch64'], inputs=tree))
    add(item('ptx', 'ptx', f'tests/ptx/run.sh {WORK}/ptx', mem=8, tools=['cuda', 'aarch64'], inputs=tree))
    add(item('talos', 'talos', 'tests/talos/run.sh', mem=2, tools=['wasm-tools', 'testsuite', 'aarch64'],
             inputs=tree, scripts=['tests/talos/run.sh']))

    ref = ['uv', 'python3', 'aarch64']
    for fn in ['SHA3_224', 'SHA3_256', 'SHA3_384', 'SHA3_512', 'SHAKE128', 'SHAKE256']:
        add(item(f'references/sha3-vectors-{fn}', 'references',
                 f'tools/leanrun --timeout 2h .lake/build/bin/sha3-vectors --only {fn}', mem=2, tools=ref,
                 inputs=tree, targets=['sha3-vectors']))
    for exe in ['crc-vectors', 'siphash-vectors', 'xxhash64-vectors']:
        add(item(f'references/{exe}', 'references', f'tools/leanrun --timeout 2h .lake/build/bin/{exe}',
                 mem=2, tools=ref, inputs=tree, targets=[exe]))
    for name in ['Sha2Vectors', 'HmacVectors']:
        add(item(f'references/{name}', 'references',
                 f'tools/leanrun --timeout 2h lake env lean --run tests/TestSupport/Hashing/{name}.lean',
                 mem=2, inputs=tree, portable=True))
    for name in ['regex', 'orderbook', 'conjunction', 'sgp4']:
        add(item(f'references/{name}', 'references', f'tests/{name}/run.sh', mem=3, tools=ref,
                 inputs=tree, scripts=[f'tests/{name}/run.sh']))

    add(item('layout/source-layout', 'layout', 'tools/source-layout', mem=1, tools=['node', 'git'],
             inputs=['docs'], primary=True, portable=True))
    add(item('layout/doc-links', 'layout', 'node tools/check-doc-links.mjs', mem=1, tools=['node', 'git'],
             inputs=['docs'], primary=True, portable=True))
    return out


def targets(root, chosen):
    """The targets of the build: the libraries, the executables of lakefile.lean that the scripts
    of the chosen items name, and the targets that the items list."""
    with open(os.path.join(root, 'lakefile.lean')) as f:
        exes = re.findall(r'^lean_exe\s+(?:«([^»]+)»|([\w.-]+))', f.read(), re.M)
    exes = [a or b for a, b in exes]
    text = []
    named = []
    for it in chosen:
        text.append(it['cmd'])
        named += it['targets']
        scripts = set(it['scripts']) | {w for w in it['cmd'].split()
                                        if re.match(r'^(tests|clightn|rocq)/.*\.(sh|py)$', w)}
        for s in sorted(scripts):
            with open(os.path.join(root, s)) as f:
                text.append(f.read())
    words = set(re.findall(r'[\w.-]+', '\n'.join(text)))
    modules = sorted({t for t in named if t not in exes})
    return LIBRARIES + [e for e in exes if e in words or e in named] + modules


# Counts.  Each function takes the runs of a step, a list of (item, log text), and the root, and
# returns the cell of the step's counts.

def c(n):
    return f'{int(n):,}'


def nouns(n, one, many):
    return f'1 {one}' if int(n) == 1 else f'{c(n)} {many}'


def pf(p, f, noun):
    return f'{c(p)} {noun} passed, {c(f)} failed'


def join(xs):
    xs = list(xs)
    if len(xs) <= 1:
        return ''.join(xs)
    if len(xs) == 2:
        return f'{xs[0]} and {xs[1]}'
    return ', '.join(xs[:-1]) + ', and ' + xs[-1]


def lines(runs):
    return [line for _, text in runs for line in text.splitlines()]


def last(pattern, text):
    found = re.findall(pattern, text, re.M)
    return found[-1] if found else None


def matches(pattern, ls):
    r = re.compile(pattern)
    return sum(1 for line in ls if r.search(line))


def checks_cell(ls):
    kernel = matches(r"^pass: the kernel's check of ", ls)
    skipped = matches(r'^skip: ', ls)
    cell = f"{c(matches(r'^pass: ', ls))} checks passed"
    if kernel == 1:
        cell += ', 1 of them a kernel check of file theorems'
    elif kernel:
        cell += f', {c(kernel)} of them kernel checks of file theorems'
    cell += f", {c(matches(r'^fail: ', ls))} failed"
    if skipped:
        cell += f', {c(skipped)} skipped'
    return cell


def audits_cell(ls):
    found = [int(m.group(1)) for line in ls
             if (m := re.search(r'axiom check passed for ([0-9]+) theorems', line))]
    if not found:
        return ''
    return f"{nouns(sum(found), 'theorem', 'theorems')} in {nouns(len(found), 'axiom audit', 'axiom audits')}"


def names_count(s):
    return 0 if s.strip() == 'none' else len(s.split())


def sum_pairs(pattern, ls):
    r = re.compile(pattern)
    found = [tuple(int(x) for x in m.groups()) for line in ls if (m := r.search(line))]
    if not found:
        return None
    return tuple(map(sum, zip(*found)))


def count_verified(runs, root, passed):
    ls = lines(runs)
    parts = []
    total = sum_pairs(r'^verified: passed ([0-9]+) failed ([0-9]+)$', ls)
    if total:
        parts.append(pf(*total, 'cases'))
    for id, group in [('verified/gpt', 'GPT'), ('verified/module-cases-euler', 'Euler'),
                      ('verified/module-cases-shapes', 'sums')]:
        got = sum_pairs(r'^passed ([0-9]+) failed ([0-9]+)$',
                        [line for it, text in runs if it['id'] == id for line in text.splitlines()])
        if got:
            parts.append(pf(*got, f'{group} cases'))
    edges = last(r'^slew edges: ([0-9]+) edges agree with native Lean', '\n'.join(ls))
    if edges:
        parts.append(f'{c(edges)} slew edges agree')
    files = matches(r': [^ ]+\.wasm holds the module of [^ ]+, with the permitted axioms$', ls)
    if files:
        parts.append(f"{nouns(files, 'file theorem', 'file theorems')} with the permitted axioms")
    a = audits_cell(ls)
    if a:
        parts.append(a)
    if passed:
        parts.append(f"{matches(r'^run: emit ', ls)} modules written and validated")
    return '; '.join(parts)


def count_native_verified(runs, root, passed):
    text = '\n'.join(lines(runs))
    cell = ''
    got = last(r'^native verified: passed ([0-9]+) failed ([0-9]+)$', text)
    if got:
        cell = pf(*got, 'cases')
    notrun = last(r'^native verified: not run: ([0-9]+) outside the translation, ([0-9]+) of ', text)
    if notrun:
        cell += f', {c(int(notrun[0]) + int(notrun[1]))} not run'
    made = last(r'^native modules: passed ([0-9]+) failed ([0-9]+)$', text)
    if made:
        cell += '; ' + pf(*made, 'module cases')
        n = last(r'^native modules: not run: ([0-9]+) outside the translation$', text)
        if n:
            cell += f', {c(n)} not run'
    lst = last(r'^native verified: modules without a translation: ?(.*)$', text)
    if lst is not None:
        cell += f"; {nouns(names_count(lst), 'module', 'modules')} without a translation"
    lst = last(r'^native verified: modules without aligned theorems: ?(.*)$', text)
    if lst is not None:
        cell += f"; {nouns(names_count(lst), 'module', 'modules')} without aligned theorems"
    return cell.removeprefix('; ')


def count_native_aligned(runs, root, passed):
    text = '\n'.join(lines(runs))
    cell = '; '.join(f'`{a}` built with {b} exports'
                     for a, b in re.findall(r'^aligned: ([^ ]+) built: ([0-9]+) exports$', text, re.M))
    refused = [f'`{a}`' for a in re.findall(r'^aligned: ([^ ]+) refused: ', text, re.M)]
    if refused:
        cell += f'; {join(refused)} refused'
    return cell.removeprefix('; ')


def count_native_run(runs, root, passed):
    found = re.findall(r'^native: [^ ]+: ([0-9]+) calls agree with Talos$', '\n'.join(lines(runs)), re.M)
    return (f"{nouns(len(found), 'program', 'programs')}, whose "
            f"{nouns(sum(map(int, found)), 'call', 'calls')} agree with Talos")


def count_native_bytes(runs, root, passed):
    text = '\n'.join(lines(runs))
    found = re.findall(r'^native bytes: [^:]+: ([0-9]+) of ([0-9]+) cases agree with Wasmtime$', text, re.M)
    cell = ''
    if found:
        cell = f'{c(sum(int(a) for a, _ in found))} of {c(sum(int(b) for _, b in found))} cases agree with Wasmtime'
    made = last(r'^native bytes: ([0-9]+) trap cases run$', text)
    if made:
        cell += f"; {nouns(made, 'trap case', 'trap cases')} run"
    return cell.removeprefix('; ')


def clight_cell(text, prefix, what):
    got = last(prefix + r': ([0-9]+) agree \(([0-9]+) undefined, ([0-9]+) trace programs, ([0-9]+) input programs\), ([0-9]+) differ, ([0-9]+) out of fuel$', text)
    if not got:
        return ''
    a, u, t, i, d, o = got
    return (f'{c(a)} programs agree with {what}, {c(u)} of them undefined, {c(t)} of them trace programs,'
            f' and {c(i)} input programs; {c(d)} differ; {c(o)} out of fuel')


def count_wasi(runs, root, passed):
    n = g = 0
    for line in lines(runs):
        m = re.search(r' passed: ([0-9]+) ([a-z]+ )?cases$', line)
        if m:
            n += int(m.group(1))
            g += 1
            continue
        m = re.search(r': ([0-9]+) cases passed$', line)
        if m:
            n += int(m.group(1))
            g += 1
    cell = f"{c(n)} cases passed in {nouns(g, 'group', 'groups')}" if g else ''
    a = audits_cell(lines(runs))
    if a:
        cell += f'; {a}'
    return cell.removeprefix('; ')


def count_baremetal_verified(runs, root, passed):
    ls = lines(runs)
    total = sum_pairs(r'^baremetal verified: total passed ([0-9]+) failed ([0-9]+) not run ([0-9]+)$', ls)
    if not total:
        return ''
    modules = matches(r'^baremetal verified: [^ ]+ passed [0-9]+ failed [0-9]+ not run [0-9]+ stack ', ls)
    cell = f"{c(total[0])} cases passed, {c(total[1])} failed, {c(total[2])} not run, in {nouns(modules, 'module', 'modules')}"
    untranslated = sum(names_count(m.group(1)) for line in ls
                       if (m := re.match(r'^baremetal verified: modules without a translation: ?(.*)$', line)))
    cell += f"; {nouns(untranslated, 'module', 'modules')} without a translation"
    unbuilt = matches(r'^baremetal verified: module that does not build: ', ls)
    cell += f"; {nouns(unbuilt, 'module that does', 'modules that do')} not build"
    return cell


def count_isla(runs, root, passed):
    ls = lines(runs)
    std = r'(propext|Classical\.choice|Quot\.sound)'
    modules = matches(r'^tests/TestSupport/[^ ]+\.lean: [0-9.]+ s', ls)
    reports = matches(r'depends on axioms|does not depend on any axioms', ls)
    permitted = matches(rf'does not depend on any axioms$|depends on axioms: \[{std}(, {std})*\]$', ls)
    failed = matches(r'^fail: ', ls)
    cell = (f"{nouns(modules, 'module', 'modules')} elaborated; {c(reports)} axiom reports,"
            f" {c(permitted)} of them with no axiom beyond `propext`, `Classical.choice`, and `Quot.sound`")
    if failed:
        cell += f"; {nouns(failed, 'failure', 'failures')}"
    return cell


def count_clightn(runs, root, passed):
    text = '\n'.join(lines(runs))
    found = last(r'^clightn: ([0-9]+) relations with ([0-9]+) constructors, ([0-9]+) constants?, and ([0-9]+) statements agree in Rocq and Lean', text)
    if not (passed and found):
        return ''
    eq = last(r'^clightn: ([0-9]+) equations agree in Rocq and Lean', text) or 0
    groups = len(re.findall(r'^clightn: the check found exactly the planted differences, [0-9]+$', text, re.M))
    return (f"{nouns(found[0], 'relation', 'relations')} with {c(found[1])} constructors, "
            f"{nouns(found[2], 'constant', 'constants')}, and {nouns(found[3], 'statement', 'statements')} agree in"
            f" Rocq and Lean, each proved in both; the step between the provers assumes"
            f" {nouns(eq, 'floating-point equation', 'floating-point equations')}; {groups} groups of planted"
            f' errors reported')


def count_wgsl_emit(mode):
    def count(runs, root, passed):
        if not passed:
            return ''
        d = os.path.join(root, WORK, f'wgsl-{mode}', 'wgsl')
        kernels = sum(1 for _, _, fs in os.walk(d) for f in fs if f.endswith('.wgsl'))
        with open(os.path.join(d, 'cases.txt')) as f:
            n = sum(1 for _ in f)
        return f"{nouns(kernels, 'kernel', 'kernels')} and {nouns(n, 'case', 'cases')} written"
    return count


def count_wgsl_drivers(runs, root, passed):
    text = '\n'.join(lines(runs))
    s = last(r'^vk_swiftshader_icd: passed ([0-9]+) failed ([0-9]+)$', text)
    l = last(r'^lvp_icd: passed ([0-9]+) failed ([0-9]+)$', text)
    return f"SwiftShader: {pf(*s, 'cases') if s else ''}; llvmpipe: {pf(*l, 'cases') if l else ''}"


def count_talos(runs, root, passed):
    text = '\n'.join(lines(runs))
    p, f, s = (last(rf'^talos: {k} ([0-9]+)$', text) for k in ('pass', 'fail', 'skip'))
    if not p:
        return ''
    cell = f'{c(p)} commands passed, {c(f)} failed, {c(s)} skipped'
    if re.search(r'^talos: the report of [0-9]+ commands equals', text, re.M):
        cell += "; report equal to Talos's"
    return cell


def count_references(runs, root, passed):
    checks = {it['id'].split('/')[1].split('-SHA')[0] for it, _ in runs}
    return f'{len(checks)} checks' if passed else ''


def simple(pattern, fmt):
    def count(runs, root, passed):
        if not passed:
            return ''
        got = last(pattern, '\n'.join(lines(runs)))
        if got is None:
            return ''
        return fmt.format(*(got if isinstance(got, tuple) else (got,)))
    return count


def passfail(name):
    def count(runs, root, passed):
        ls = lines(runs)
        return f"{matches(r'^pass: ', ls)} {name} passed, {matches(r'^fail: ', ls)} failed"
    return count


def count_vkb(runs, root, passed):
    d = os.path.join(root, 'VKB/entries')
    n = sum(1 for e in os.listdir(d) if os.path.isdir(os.path.join(d, e)))
    return f'{n} entries' + (', no problem reported' if passed else '')


COUNTS = {
    'axioms': lambda runs, root, passed: (lambda n: f'{n} declarations' if n else '')(
        last(r'^axioms: ([0-9]+) declarations of the repository', '\n'.join(lines(runs)))),
    'verified': count_verified,
    'drone': lambda runs, root, passed: (lambda a, b: f"{pf(*a, 'calls')}; {pf(*b, 'terrains')}; expected results from the reference implementation" if a and b else '')(
        last(r'^drone calls in WebAssembly: ([0-9]+) cases, ([0-9]+) failed$', '\n'.join(lines(runs))),
        last(r'^drone corpus in WebAssembly: ([0-9]+) cases, ([0-9]+) failed$', '\n'.join(lines(runs)))),
    'chunks': lambda runs, root, passed: (lambda a: pf(*a, 'cases') if a else '')(
        last(r'^chunks: ([0-9]+) cases, ([0-9]+) failed$', '\n'.join(lines(runs)))),
    'native-verified': count_native_verified,
    'native-verified-aligned': count_native_verified,
    'native-aligned': count_native_aligned,
    'native-run': count_native_run,
    'native-bytes': count_native_bytes,
    'native-clight': lambda runs, root, passed: clight_cell('\n'.join(lines(runs)), '^clight', '`ccomp -interp`'),
    'wasi': count_wasi,
    'wasi-sys': simple(r'^flat call Wasmtime cases passed: ([0-9]+)$', '{} cases passed'),
    'random-histogram': simple(r'^random histogram: ([0-9]+) runs passed$', '{} runs passed'),
    'random-choice': simple(r'^random choice: ([0-9]+) runs passed$', '{} runs passed'),
    'manifest-check': simple(r'^manifest check: ([0-9]+) runs passed, ([0-9]+) verdicts agree with sha256sum -c$',
                             '{} runs passed, {} verdicts'),
    'linux-sys': simple(r'^linux frame cases passed: ([0-9]+)$', '{} frame test runs passed'),
    'a64-elf': lambda runs, root, passed: checks_cell(lines(runs)),
    'a64-wasi': lambda runs, root, passed: checks_cell(lines(runs)),
    'a64-wasi-clocks': lambda runs, root, passed: checks_cell(lines(runs)),
    'a64-wasi-preopen': lambda runs, root, passed: checks_cell(lines(runs)),
    'a64-wasi-files': lambda runs, root, passed: checks_cell(lines(runs)),
    'baremetal-run': simple(r'^baremetal: (.*) pass under TCG$', '{} pass'),
    'baremetal-programs': passfail('programs'),
    'baremetal-inputs': passfail('inputs'),
    'baremetal-ctl': passfail('ctl'),
    'baremetal-verified': count_baremetal_verified,
    'a64-images': lambda runs, root, passed: checks_cell(lines(runs)),
    'a64-uart': lambda runs, root, passed: checks_cell(lines(runs)),
    'isla': count_isla,
    'm7-isla': count_isla,
    'vkb': count_vkb,
    'rocq': simple(r'^rocq: Clight2Asm\.v checks, with the assumptions of transf_c_program_correct and (.*)$',
                   '`Clight2Asm.v` checks, with the assumptions of `transf_c_program_correct` and `{}`'),
    'clight-rocq': lambda runs, root, passed: clight_cell('\n'.join(lines(runs)), '^clight-rocq', 'the Rocq evaluator'),
    'clightn': count_clightn,
    'wgsl-verified-emit': count_wgsl_emit('verified'),
    'wgsl-default-emit': count_wgsl_emit('default'),
    'wgsl-verified-drivers': count_wgsl_drivers,
    'wgsl-default-drivers': count_wgsl_drivers,
    'talos': count_talos,
    'references': count_references,
}


def counts(step, runs, root, passed):
    f = COUNTS.get(step)
    return f(runs, root, passed) if f else ''
