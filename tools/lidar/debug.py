#!/usr/bin/env python3
"""Capture a bounded debugger trace of a lidar certificate check."""
import argparse
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('--local', action='store_true',
                        help='use already-authorized Lean execution without systemd limits')
    args = parser.parse_args()
    source = args.source.resolve()
    env = dict(os.environ)
    if args.local:
        env['LEANRUN_LOCAL'] = '1'
    env['LEANRUN_TOOLCHAIN'] = str(ROOT/'build/tools/lean-4.34.0-rc2-linux')
    env['LEAN_PATH'] = str(source.parent)
    debugger = ROOT/'build/lidar/debugger/usr'
    env['LD_LIBRARY_PATH'] = str(debugger/'lib/x86_64-linux-gnu')
    command = [str(ROOT/'tools/leanrun'), '--timeout', '3m', 'lake', '-d',
        'proofs/talos/lean', 'env', str(debugger/'bin/gdb'), '--batch',
        '-ex', 'run', '-ex', 'bt 30', '--args', 'lean', '-M', '8192', '--run',
        'tools/lidar/Check.lean', str(source), str(source.with_suffix('.debug.olean'))]
    log = ROOT/'build/lidar/checks'/f'{source.stem.lower()}-debugger.log'
    with log.open('w') as stream:
        result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    print(log.read_text()[-12000:])
    print(f'Debugger log: {log}')
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
