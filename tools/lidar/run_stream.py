#!/usr/bin/env python3
"""Exercise summary-only requests, pose/range invalidation, and rejected updates."""
import argparse
import json
from pathlib import Path
if __package__:
    from .run import ROOT, Scan, configure_cli
    from .run_interval import IntervalScan, expected
else:
    from run import ROOT, Scan, configure_cli
    from run_interval import IntervalScan, expected


def exercise(mode, bundle):
    cardinal = mode == 'cardinal'
    interval = mode == 'interval'
    scene = ([[120,90,130,110], [140,95,150,105], [95,160,105,170], [20,80,40,95]]
             if cardinal else [[120,120,130,150], [130,140,140,160], [60,140,80,160], [120,60,130,80]])
    runner = (IntervalScan if interval else Scan)(bundle, scene)
    distance, short = (60,19) if cardinal else (3600,1800)
    mask_second = 4 if cardinal else 2
    hit_all = {'hits':2,'nearest':20} if cardinal else {'hits':3,'nearest':2000}
    hit_first = {'hits':1,'nearest':20 if cardinal else 2000}
    hit_second = {'hits':1,'nearest':60 if cardinal else 3000}
    miss = {'hits':0,'nearest':None}
    if interval:
        hit_all = expected('hit',3,3,1900,2100)
        hit_first = expected('hit',1,1,1900,2100)
        hit_second = expected('hit',1,1,2925,3075)
        miss = expected('miss',0,0)
    cases = [
        ('first scan', [100,100,distance,15], hit_all, True),
        ('first beam summary only', [100,100,distance,1], hit_first, False),
        ('second beam summary only', [100,100,distance,mask_second], hit_second, False),
        ('miss summary only', [100,100,distance,8], miss, False),
        ('summary after rejected update', [100,100,distance,mask_second], hit_second, False),
        ('moved sensor', [200,200,20 if cardinal else 1200,15], miss, True),
        ('moved summary only', [200,200,20 if cardinal else 1200,1], miss, False),
        ('returned sensor', [100,100,distance,15], hit_all, True),
        ('changed range', [100,100,short,15], miss, True),
        ('restored range', [100,100,distance,1], hit_first, True),
        ('final summary only', [100,100,distance,15], hit_all, False),
    ]
    records = []
    for index, (name, params, want, fresh) in enumerate(cases):
        if index == 4:
            before = dict(runner.counters)
            try:
                runner.scan(100,100,distance,16)
            except ValueError:
                pass
            else:
                raise AssertionError('invalid mask accepted')
            assert runner.counters == before, 'rejected update changed transfer counters'
        previous = dict(runner.counters)
        actual = runner.scan(*params)
        assert actual == want, (mode,name,want,actual)
        delta = {k:runner.counters[k]-previous[k] for k in runner.counters}
        assert delta['scans'] == int(fresh), (mode,name,delta)
        assert delta['dispatches'] == (2 if interval else 1)*(1+int(fresh))
        assert delta['parameter_upload_bytes'] == 16
        assert delta['readback_bytes'] == (8 if interval else 4)
        assert delta['scene_upload_bytes'] == delta['direction_upload_bytes'] == 0
        records.append({'name':name,'parameters':params,'expected':want,'observed':actual,
                        'fresh_scan':fresh,'transfer_delta':delta})
    assert runner.counters['queries'] == 11 and runner.counters['scans'] == 5
    assert runner.counters['dispatches'] == (32 if interval else 16)
    return {'mode':mode,'adapter':dict(runner.adapter.info),'cases':records,
            'counters':runner.counters,'rejections':1,'artifacts':runner.digests}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=ROOT/'build/lidar')
    parser.add_argument('--output', type=Path, default=ROOT/'build/lidar/stream-run.json')
    args = parser.parse_args()
    evidence = {'modes':[exercise(mode,args.root/folder) for mode,folder in
                         [('cardinal','bundle'),('oblique','oblique'),('interval','interval')]]}
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(evidence,indent=2)+'\n')
    print(json.dumps(evidence,indent=2))


if __name__ == '__main__':
    configure_cli()
    main()
