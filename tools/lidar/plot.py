#!/usr/bin/env python3
"""Draw the actual four requested observations retained by a lidar run as SVG."""
import json
from fractions import Fraction
from html import escape
from pathlib import Path
import sys

source = Path(sys.argv[1] if len(sys.argv) > 1 else 'build/lidar/run.json')
out = Path(sys.argv[2] if len(sys.argv) > 2 else 'docs/lidar/figures/cardinal.svg')
evidence = json.loads(source.read_text())
oblique = evidence.get('mode') == 'oblique'
ticks = evidence.get('ticks_per_unit', 1)
reference = evidence['cases'][0]['parameters'][:3]
sensor_x, sensor_y, range_word = reference
range_units = Fraction(range_word, ticks)
by_mask = {row['parameters'][3]: row['observed'] for row in evidence['cases']
           if row['parameters'][:3] == reference}
vectors = [(Fraction(x,5),Fraction(y,5)) for x,y in evidence['direction_numerators']] if oblique else [(1,0),(-1,0),(0,1),(0,-1)]
labels = ['NE','NW','SE','SW'] if oblique else ['East','West','North','South']
scale = 2.5
point = lambda x, y: (45 + x*scale, 560-y*scale)
parts = ['<svg xmlns="http://www.w3.org/2000/svg" width="740" height="630" viewBox="0 0 740 630">',
         '<rect width="740" height="630" fill="#f8fafc"/>',
         '<g font-family="system-ui,sans-serif" fill="#172033">',
         '<text x="30" y="30" font-size="22">Lidar scan · actual WebGPU summaries</text>',
         f'<text x="30" y="54" font-size="13">Closed rectangles · {"oblique" if oblique else "cardinal"} beams · sensor ({sensor_x}, {sensor_y}) · range {range_units}</text>']
for k in range(0, 181, 20):
    x,y = point(k,0)
    parts += [f'<path d="M{x} 90 V560" stroke="#dce3eb"/>', f'<text x="{x-8}" y="580" font-size="10">{k}</text>']
    x,y = point(0,k)
    if y >= 90:
        parts += [f'<path d="M45 {y} H550" stroke="#dce3eb"/>',f'<text x="18" y="{y+4}" font-size="10">{k}</text>']
for i,(x0,y0,x1,y1) in enumerate(evidence['scene']):
    x,y=point(x0,y1)
    parts.append(f'<rect x="{x}" y="{y}" width="{(x1-x0)*scale}" height="{(y1-y0)*scale}" fill="#cbd5e1" stroke="#64748b"/>')
    parts.append(f'<text x="{x+3}" y="{y+12}" font-size="11">{i}</text>')
x0,y0=point(sensor_x,sensor_y)
for i,(dx,dy) in enumerate(vectors):
    observation=by_mask[1<<i]
    hit=observation['nearest'] is not None
    distance=Fraction(observation['nearest'], ticks) if hit else range_units
    x1,y1=point(float(sensor_x+dx*distance),float(sensor_y+dy*distance))
    color='#047857' if hit else '#b45309'
    parts.append(f'<path d="M{x0} {y0} L{x1} {y1}" stroke="{color}" stroke-width="3"'+(' stroke-dasharray="7 5"' if not hit else '')+'/>')
    parts.append(f'<circle cx="{x1}" cy="{y1}" r="4" fill="{color}"/>')
    parts.append(f'<text x="575" y="{115+i*26}" font-size="13">{labels[i]}: {distance if hit else "miss"}</text>')
nearest = by_mask[15]['nearest']
nearest_units = str(Fraction(nearest,ticks)) if nearest is not None else 'none'
parts += [f'<circle cx="{x0}" cy="{y0}" r="6" fill="#1d4ed8"/>',
          f'<text x="575" y="245" font-size="13">Nearest: {nearest_units} units</text>',
          f'<text x="575" y="270" font-size="13">Hit count: {by_mask[15]["hits"]}</text>',
          '<text x="575" y="320" font-size="12">4-byte summary</text>',
          '<text x="575" y="340" font-size="12">16-byte parameters</text>',
          f'<text x="30" y="613" font-size="12">{escape(evidence["adapter"]["backend_type"])} · {escape(evidence["adapter"]["adapter_type"])} adapter · observations checked separately from proofs</text>',
          '</g></svg>']
out.parent.mkdir(parents=True,exist_ok=True)
out.write_text('\n'.join(parts)+'\n')
print(out)
