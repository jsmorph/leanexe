#!/usr/bin/env python3
"""Independent decimal-log oracle; input floats are interpreted exactly."""
import json
import sys
from decimal import Decimal, localcontext

with localcontext() as ctx:
    ctx.prec = 100
    results = []
    for delta in json.load(sys.stdin):
        d = Decimal.from_float(float(delta))
        t = 1 + d
        h = (t*t.ln()-t+1)/(d*d) if d else Decimal('0.5')
        results.append(str(h))
    print(json.dumps(results))
