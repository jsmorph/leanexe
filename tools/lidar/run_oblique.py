#!/usr/bin/env python3
"""Compare the resident oblique scan with known exact rational geometry."""
import argparse
import json
from pathlib import Path

if __package__:
    from .run import ROOT, Scan, configure_cli
else:
    from run import ROOT, Scan, configure_cli


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--bundle', type=Path, default=ROOT/'build/lidar/oblique')
    parser.add_argument('--output', type=Path, default=ROOT/'build/lidar/oblique-run.json')
    args = parser.parse_args()
    receipt = json.loads((args.bundle/'checked.json').read_text())
    if receipt.get('mode') != 'oblique':
        raise ValueError('this demonstration requires a checked oblique bundle')
    scene = [[120,120,130,150], [130,140,140,160], [60,140,80,160], [120,60,130,80]]
    runner = Scan(args.bundle, scene)
    cases = [
        ('three reflected directions', [100,100,3600,15], {'hits':3,'nearest':2000}),
        ('northeast occlusion', [100,100,3600,1], {'hits':1,'nearest':2000}),
        ('northwest', [100,100,3600,2], {'hits':1,'nearest':3000}),
        ('northwest exact range', [100,100,3000,2], {'hits':1,'nearest':3000}),
        ('southeast', [100,100,3600,4], {'hits':1,'nearest':2000}),
        ('southwest miss', [100,100,3600,8], {'hits':0,'nearest':None}),
        ('range below intersections', [100,100,1999,15], {'hits':0,'nearest':None}),
        ('range at intersections', [100,100,2000,15], {'hits':2,'nearest':2000}),
        ('origin inside', [125,140,3600,15], {'hits':4,'nearest':0}),
        ('tangent corner', [100,80,3000,1], {'hits':1,'nearest':3000}),
        ('before tangent corner', [100,80,2999,1], {'hits':0,'nearest':None}),
        ('below tangent corner', [100,79,3600,1], {'hits':0,'nearest':None}),
        ('empty request', [100,100,3600,0], {'hits':0,'nearest':None}),
        ('return to original scan', [100,100,3600,15], {'hits':3,'nearest':2000}),
    ]
    records = []
    for name, parameters, expected in cases:
        observed = runner.scan(*parameters)
        if observed != expected:
            raise AssertionError((name, expected, observed))
        records.append({'name':name, 'parameters':parameters, 'expected':expected, 'observed':observed})
    evidence = {'adapter':dict(runner.adapter.info), 'scene':scene, 'cases':records,
                'counters':runner.counters, 'artifacts':runner.digests,
                'mode':'oblique', 'ticks_per_unit':60,
                'direction_numerators':[[3,4],[-3,4],[3,-4],[-3,-4]], 'direction_denominator':5}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps(evidence,indent=2))


if __name__ == '__main__':
    configure_cli()
    main()
