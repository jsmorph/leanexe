#!/usr/bin/env python3
"""Compare native Wasm/WebGPU execution to retained Lean output words."""
import json
from pathlib import Path
import shutil
import struct
import subprocess
import sys
import tempfile

root, bundle = map(Path, sys.argv[1:])
runner = bundle / 'gpt128'
references = json.loads((bundle / 'reference.json').read_text())
evidence = Path(tempfile.mkdtemp(prefix='demo-test-', dir=root / 'build'))
results = []
for case in references:
    weights = evidence / (case['name'] + '.bin')
    weights.write_bytes(b''.join(struct.pack('<Q', int(w)) for w in case['preparedWeights']))
    trace = evidence / (case['name'] + '.jsonl')
    result = subprocess.run([str(runner), str(bundle), '--tokens', ','.join(map(str, case['tokens'])),
                             '--generate', '1', '--trace', str(trace), '--test-weights', str(weights)],
                            capture_output=True, timeout=45)
    (evidence / (case['name'] + '.stderr')).write_bytes(result.stderr)
    assert result.returncode == 0, result.stderr.decode(errors='replace')
    actual = json.loads(trace.read_text())
    for field in ('hidden', 'headWords', 'logits'):
        assert actual[field] == case[field], f"{case['name']}: {field} differs from Lean"
    logits = [struct.unpack('<d', struct.pack('<Q', int(w)))[0] for w in case['logits']]
    assert actual['token'] == max(range(256), key=logits.__getitem__)
    results.append({'name': case['name'], 'status': 'pass'})
# A full context must keep working after the window slides, without stale GPU data.
trace = evidence / 'generation.jsonl'
run = subprocess.run([str(runner), str(bundle), '--prompt', 'To be, or not to be',
                      '--generate', '160', '--trace', str(trace)], capture_output=True, timeout=60)
assert run.returncode == 0, run.stderr.decode(errors='replace')
lines = [json.loads(line) for line in trace.read_text().splitlines()]
assert len(lines) == 160 and all(0 <= x['token'] < 256 for x in lines)
assert run.stdout == b'To be, or not to be' + bytes(x['token'] for x in lines) + b'\n'
(evidence / 'generation.txt').write_bytes(run.stdout)
# Parse errors fail before any WebGPU initialization.
for args in (['--prompt', ''], ['--prompt', 'a'*129], ['--tokens', '256'],
             ['--tokens', '1,'], ['--prompt', 'a', '--generate', '0'],
             ['--prompt', 'a', '--generate', '1025']):
    result = subprocess.run([str(runner), str(bundle), *args], capture_output=True, timeout=10)
    assert result.returncode != 0 and b'WebGPU:' not in result.stderr
# The executable is bound to its actual build artifacts, not merely file names.
altered = evidence / 'altered'
altered.mkdir()
for name in ('hidden.wasm', 'transfer.wasm', 'finish.wasm', 'kernel.wgsl', 'weights.bin'):
    shutil.copyfile(bundle / name, altered / name)
with (altered / 'kernel.wgsl').open('ab') as f:
    f.write(b'\n// altered\n')
result = subprocess.run([str(runner), str(altered), '--prompt', 'a'], capture_output=True, timeout=10)
assert result.returncode != 0 and b'SHA-256 differs' in result.stderr
report = {'status': 'pass', 'cases': results, 'checkedHiddenWords': 32,
          'checkedHeadWords': 2048, 'checkedLogitWords': 2048,
          'generatedBytes': 160, 'invalidInputsRejected': 6, 'alteredShaderRejected': True}
(evidence / 'result.json').write_text(json.dumps(report, indent=2) + '\n')
print(f'Passed: {evidence}')
