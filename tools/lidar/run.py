#!/usr/bin/env python3
"""Resident cardinal-lidar WebGPU demonstration. No CPU ray tracing in the host."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
import sys
from artifacts import checked_artifacts

ROOT = Path(__file__).resolve().parents[2]
VULKAN = ROOT / 'build/lidar/vulkan'
if VULKAN.exists() and not os.environ.get('LEANEXE_LIDAR_CONFIGURED'):
    env = dict(os.environ, LEANEXE_LIDAR_CONFIGURED='1')
    env['LD_LIBRARY_PATH'] = str(VULKAN / 'usr/lib/x86_64-linux-gnu') + ':' + env.get('LD_LIBRARY_PATH', '')
    env.setdefault('VK_DRIVER_FILES', str(VULKAN / 'usr/share/vulkan/icd.d/lvp_icd.json'))
    env.setdefault('XDG_RUNTIME_DIR', '/tmp')
    cache = ROOT / 'build/lidar/gpu-cache'
    cache.mkdir(parents=True, exist_ok=True)
    env.setdefault('XDG_CACHE_HOME', str(cache))
    os.execve(sys.executable, [sys.executable, *sys.argv], env)

import wgpu
import wasmtime


def words(values):
    return struct.pack('<' + 'I' * len(values), *values)


class Scan:
    def __init__(self, bundle, rectangles):
        artifacts = checked_artifacts(bundle)
        self.digests = {name: hashlib.sha256(data).hexdigest() for name, data in artifacts.items()}
        if len(rectangles) != 4 or any(len(b) != 4 or not
                (0 <= b[0] <= b[2] <= 4095 and 0 <= b[1] <= b[3] <= 4095) for b in rectangles):
            raise ValueError('scene requires four closed rectangles in [0,4095]^2')
        self.adapter = wgpu.gpu.request_adapter_sync(power_preference='low-power')
        self.device = self.adapter.request_device_sync()
        self.scene = self.device.create_buffer_with_data(data=words(sum(rectangles, [])), usage=wgpu.BufferUsage.STORAGE)
        self.directions = self.device.create_buffer_with_data(data=words([0, 1, 2, 3]), usage=wgpu.BufferUsage.STORAGE)
        self.params = self.device.create_buffer(size=16, usage=wgpu.BufferUsage.STORAGE | wgpu.BufferUsage.COPY_DST)
        self.results = self.device.create_buffer(size=16, usage=wgpu.BufferUsage.STORAGE)
        self.summary = self.device.create_buffer(size=16, usage=wgpu.BufferUsage.STORAGE | wgpu.BufferUsage.COPY_SRC)
        self.pipelines = []
        self.groups = []
        for name, inp, out in [('scan.wgsl', self.scene, self.results), ('summary.wgsl', self.results, self.summary)]:
            code = artifacts[name].decode('utf-8')
            module = self.device.create_shader_module(code=code)
            pipeline = self.device.create_compute_pipeline(layout='auto', compute={'module': module, 'entry_point': 'lidar'})
            # Auto layouts omit the direction binding when the summary does not read it.
            bindings = [(0, inp), (2, self.params), (3, out)]
            if name == 'scan.wgsl':
                bindings.insert(1, (1, self.directions))
            entries = [{'binding': i, 'resource': {'buffer': b, 'offset': 0, 'size': b.size}} for i, b in bindings]
            self.pipelines.append(pipeline)
            self.groups.append(self.device.create_bind_group(layout=pipeline.get_bind_group_layout(0), entries=entries))
        self.engine = wasmtime.Engine()
        self.store = wasmtime.Store(self.engine)
        self.wasm = wasmtime.Instance(self.store, wasmtime.Module(self.engine, artifacts['controller.wasm']), [])
        self.controller = self.wasm.exports(self.store)['parameters']
        self.counters = {'scene_upload_bytes': 64, 'direction_upload_bytes': 16, 'parameter_upload_bytes': 0,
                         'readback_bytes': 0, 'scans': 0, 'dispatches': 0}

    def scan(self, x, y, distance, mask):
        for value in [x, y, distance, mask]:
            if not isinstance(value, int) or not 0 <= value < 2**63:
                raise ValueError('parameters must be nonnegative signed-i64-compatible integers')
        packed = self.controller(self.store, x, y, distance, mask)
        if packed == -1:
            raise ValueError('WASM rejected scan parameters')
        params = [packed & 4095, (packed >> 12) & 4095, (packed >> 24) & 4095, (packed >> 36) & 15]
        self.device.queue.write_buffer(self.params, 0, words(params))
        encoder = self.device.create_command_encoder()
        for pipeline, group in zip(self.pipelines, self.groups):
            compute = encoder.begin_compute_pass()
            compute.set_pipeline(pipeline)
            compute.set_bind_group(0, group)
            compute.dispatch_workgroups(1)
            compute.end()
        self.device.queue.submit([encoder.finish()])
        summary, = struct.unpack('<I', self.device.queue.read_buffer(self.summary, 0, 4))
        self.counters['parameter_upload_bytes'] += 16
        self.counters['readback_bytes'] += 4
        self.counters['scans'] += 1
        self.counters['dispatches'] += 2
        return {'hits': summary // 8192, 'nearest': None if summary % 8192 > distance else summary % 8192}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=ROOT / 'build/lidar/bundle')
    parser.add_argument('--output', type=Path, default=ROOT / 'build/lidar/run.json')
    args = parser.parse_args()
    scene = [[120,90,130,110], [140,95,150,105], [95,160,105,170], [20,80,40,95]]
    runner = Scan(args.bundle, scene)
    cases = [
        ('occlusion and inclusive range', [100,100,60,15], {'hits':2,'nearest':20}),
        ('east only', [100,100,60,1], {'hits':1,'nearest':20}),
        ('south miss', [100,100,60,8], {'hits':0,'nearest':None}),
        ('north only', [100,100,60,4], {'hits':1,'nearest':60}),
        ('west miss', [100,100,60,2], {'hits':0,'nearest':None}),
        ('range below obstacle', [100,100,19,15], {'hits':0,'nearest':None}),
        ('range on obstacle', [100,100,20,15], {'hits':1,'nearest':20}),
        ('origin inside', [125,100,60,15], {'hits':4,'nearest':0}),
        ('tangent to north edge', [95,100,60,4], {'hits':1,'nearest':60}),
        ('all miss after moving', [200,200,20,15], {'hits':0,'nearest':None}),
        ('empty request', [100,100,60,0], {'hits':0,'nearest':None}),
        ('return to original scan', [100,100,60,15], {'hits':2,'nearest':20}),
    ]
    records = []
    for name, params, expected in cases:
        actual = runner.scan(*params)
        if actual != expected:
            raise AssertionError((name, expected, actual))
        records.append({'name': name, 'parameters': params, 'expected': expected, 'observed': actual})
    for params in [(4096,100,60,15), (100,100,4096,15), (100,100,60,16)]:
        try:
            runner.scan(*params)
        except ValueError:
            pass
        else:
            raise AssertionError(('invalid parameters accepted', params))
    evidence = {'adapter': dict(runner.adapter.info), 'scene': scene, 'cases': records,
                'counters': runner.counters, 'rejections': 3,
                'artifacts': runner.digests}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence, indent=2)+'\n')
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    main()
