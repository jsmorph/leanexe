#!/usr/bin/env python3
"""Plot interval summaries from retained execution evidence, without ray tracing."""
from fractions import Fraction
from html import escape
import json
from pathlib import Path
import sys

source = Path(sys.argv[1] if len(sys.argv) > 1 else 'build/lidar/interval-run.json')
out = Path(sys.argv[2] if len(sys.argv) > 2 else 'docs/lidar/figures/interval.svg')
evidence = json.loads(source.read_text())
assert evidence['mode'] == 'interval'
reference = evidence['cases'][0]['parameters'][:3]
by_mask = {r['parameters'][3]: r['observed'] for r in evidence['cases'] if r['parameters'][:3] == reference}
parts = ['<svg xmlns="http://www.w3.org/2000/svg" width="860" height="500" viewBox="0 0 860 500">',
         '<rect width="860" height="500" fill="#f8fafc"/>',
         '<g font-family="system-ui,sans-serif" fill="#172033">',
         '<text x="28" y="32" font-size="22">Lidar · conservative distance intervals</text>',
         '<text x="28" y="58" font-size="13">Actual WebGPU summaries · rectangle endpoint uncertainty ±1 grid unit</text>']
scale = 2.7
point = lambda x,y: (30+(x-40)*scale, 400-(y-60)*scale)
for x0,y0,x1,y1 in evidence['scene']:
    for delta,fill,stroke in [(1,'#fef3c7','#d97706'),(0,'#cbd5e1','#64748b'),(-1,'#a7f3d0','#047857')]:
        x,y=point(x0-delta,y1+delta)
        parts.append(f'<rect x="{x}" y="{y}" width="{(x1-x0+2*delta)*scale}" height="{(y1-y0+2*delta)*scale}" fill="{fill}" stroke="{stroke}"/>')
sx,sy,_=reference
x0,y0=point(sx,sy)
for i,(dx,dy) in enumerate([(3,4),(-3,4),(3,-4),(-3,-4)]):
    obs=by_mask[1<<i]
    distance=Fraction(obs['lower_ticks'],60) if obs['status']=='hit' else Fraction(reference[2],60)
    x1,y1=point(float(sx+dx*distance/5),float(sy+dy*distance/5))
    color='#047857' if obs['status']=='hit' else '#b45309'
    parts.append(f'<path d="M{x0} {y0} L{x1} {y1}" stroke="{color}" stroke-width="2"'+(' stroke-dasharray="6 4"' if obs['status']!='hit' else '')+'/>')
    label='certified miss'
    if obs['status']=='hit':
        upper=Fraction(obs['upper_ticks'],60)
        x2,y2=point(float(sx+dx*upper/5),float(sy+dy*upper/5))
        parts.append(f'<path d="M{x1} {y1} L{x2} {y2}" stroke="#d97706" stroke-width="8" stroke-linecap="round"/>')
        label=f'[{distance}, {upper}]'
    parts.append(f'<text x="480" y="{115+i*30}" font-size="15">{["NE","NW","SE","SW"][i]}: {label}</text>')
parts += [f'<circle cx="{x0}" cy="{y0}" r="5" fill="#1d4ed8"/>',
          '<text x="480" y="255" font-size="15">Nearest midpoint: 100/3 units</text>',
          '<text x="480" y="280" font-size="15">Proved error bound: 5/3 units</text>',
          '<text x="480" y="330" font-size="13">Amber: outer rectangle / distance band</text>',
          '<text x="480" y="354" font-size="13">Green: inner rectangle / certain hit</text>',
          '<text x="480" y="390" font-size="13">Tangent case: explicitly uncertain</text>',
          '<text x="480" y="414" font-size="13">8 summary bytes read per request</text>',
          f'<text x="28" y="478" font-size="12">{escape(evidence["adapter"]["backend_type"])} · {escape(evidence["adapter"]["adapter_type"])} adapter · physical distances shown</text>',
          '</g></svg>']
# The displayed midpoint/bound must agree with the execution evidence.
assert by_mask[15]['midpoint']=='100/3' and by_mask[15]['error_bound']=='5/3'
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text('\n'.join(parts)+'\n')
print(out)
