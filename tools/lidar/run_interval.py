#!/usr/bin/env python3
"""Resident interval lidar: exact GPU arithmetic, explicit input uncertainty."""
import argparse
from fractions import Fraction
import json
from pathlib import Path
import struct
if __package__:
    from .run import ROOT, Scan, words, wgpu, configure_cli
else:
    from run import ROOT, Scan, words, wgpu, configure_cli


class IntervalScan(Scan):
    def __init__(self, bundle, rectangles):
        if len(rectangles) != 4 or any(len(b) != 4 or not
                (1 <= b[0] and b[0]+2 <= b[2] <= 4094 and
                 1 <= b[1] and b[1]+2 <= b[3] <= 4094) for b in rectangles):
            raise ValueError('interval scene requires four rectangles with endpoints in [1,4094] and width/height >= 2')
        super().__init__(bundle, rectangles)
        if 'inner.wgsl' not in self.artifacts:
            raise ValueError('interval mode requires a checked interval bundle')
        self.inner_results = self.device.create_buffer(size=16, usage=wgpu.BufferUsage.STORAGE)
        self.inner_summary = self.device.create_buffer(size=16, usage=wgpu.BufferUsage.STORAGE | wgpu.BufferUsage.COPY_SRC)
        self.add_pipeline('inner.wgsl', self.scene, self.inner_results)
        self.add_pipeline('summary.wgsl', self.inner_results, self.inner_summary)

    def scan(self, x, y, distance, mask):
        params = self.parameter_words(x, y, distance, mask)
        pose = tuple(params[:3])
        reuse = pose == self._pose
        self._pose = None
        self.device.queue.write_buffer(self.params, 0, words(params))
        encoder = self.device.create_command_encoder()
        selected = [1, 3] if reuse else [0, 1, 2, 3]
        for index in selected:
            pipeline, group = self.pipelines[index], self.groups[index]
            compute = encoder.begin_compute_pass()
            compute.set_pipeline(pipeline)
            compute.set_bind_group(0, group)
            compute.dispatch_workgroups(1)
            compute.end()
        self.device.queue.submit([encoder.finish()])
        outer, = struct.unpack('<I', self.device.queue.read_buffer(self.summary, 0, 4))
        inner, = struct.unpack('<I', self.device.queue.read_buffer(self.inner_summary, 0, 4))
        self.counters['parameter_upload_bytes'] += 16
        self.counters['readback_bytes'] += 8
        self._pose = pose
        self.counters['queries'] += 1
        self.counters['scans'] += int(not reuse)
        self.counters['dispatches'] += len(selected)
        lower, upper = outer % 8192, inner % 8192
        status = 'miss' if lower > distance else 'hit' if upper <= distance else 'uncertain'
        return {'status': status, 'possible_hits': outer // 8192, 'certain_hits': inner // 8192,
                'lower_ticks': None if lower > distance else lower,
                'upper_ticks': None if upper > distance else upper,
                'midpoint': str(Fraction(lower+upper, 120)) if status == 'hit' else None,
                'error_bound': str(Fraction(upper-lower, 120)) if status == 'hit' else None}


def expected(status, possible, certain, lower=None, upper=None):
    return {'status': status, 'possible_hits': possible, 'certain_hits': certain,
            'lower_ticks': lower, 'upper_ticks': upper,
            'midpoint': str(Fraction(lower+upper,120)) if status == 'hit' else None,
            'error_bound': str(Fraction(upper-lower,120)) if status == 'hit' else None}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=ROOT/'build/lidar/interval')
    parser.add_argument('--output', type=Path, default=ROOT/'build/lidar/interval-run.json')
    args = parser.parse_args()
    scene = [[120,120,130,150], [130,140,140,160], [60,140,80,160], [120,60,130,80]]
    runner = IntervalScan(args.bundle, scene)
    cases = [
        ('nearest selected interval', [100,100,3600,15], expected('hit',3,3,1900,2100)),
        ('NE interval', [100,100,3600,1], expected('hit',1,1,1900,2100)),
        ('NW interval', [100,100,3600,2], expected('hit',1,1,2925,3075)),
        ('SE interval', [100,100,3600,4], expected('hit',1,1,1900,2100)),
        ('SW certified miss', [100,100,3600,8], expected('miss',0,0)),
        ('range uncertain', [100,100,3000,2], expected('uncertain',1,0,2925)),
        ('corner tangent uncertain', [100,80,3000,1], expected('uncertain',1,0,2925)),
        ('just below corner uncertain', [100,79,3000,1], expected('uncertain',1,0,3000)),
        ('outside uncertainty band', [100,77,3600,1], expected('miss',0,0)),
        ('origin certainly inside', [125,140,3600,15], expected('hit',4,4,0,0)),
        ('empty request', [100,100,3600,0], expected('miss',0,0)),
        ('return to original query', [100,100,3600,15], expected('hit',3,3,1900,2100)),
    ]
    records = []
    for name, params, want in cases:
        observed = runner.scan(*params)
        if observed != want:
            raise AssertionError((name, want, observed))
        records.append({'name': name, 'parameters': params, 'expected': want, 'observed': observed})
    for params in [(4096,100,60,15), (100,100,4096,15), (100,100,60,16)]:
        try:
            runner.scan(*params)
        except ValueError:
            pass
        else:
            raise AssertionError(('invalid parameters accepted', params))
    for invalid in [[0,120,130,150], [120,120,121,150], [120,120,4095,150]]:
        try:
            IntervalScan(args.bundle, [invalid, *scene[1:]])
        except ValueError:
            pass
        else:
            raise AssertionError(('invalid interval scene accepted', invalid))
    evidence = {'mode': 'interval', 'ticks_per_unit': 60, 'endpoint_error': 1,
                'adapter': dict(runner.adapter.info), 'scene': scene, 'cases': records,
                'counters': runner.counters, 'rejections': 3, 'scene_rejections': 3, 'artifacts': runner.digests}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence, indent=2)+'\n')
    print(json.dumps(evidence, indent=2))


if __name__ == '__main__':
    configure_cli()
    main()
