# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""The moduli M_k(x)² = J_k(x)² + Y_k(x)² around the turning point k = x.

Usage: uv run tools/bessel/turning.py X [X ...], for integers X ≥ 2.

For each X it prints, over the integer orders k < X, the largest value of
S = (π/2) √(X² − k²) M_k(X)², whose bound S ≤ 1 would give the weight bound
(π X/2) M_k² ≤ X/√(X² − k²), and the largest weight (π X/2) M_k² over all k ≤ X with
X^(1/3), the growth of that weight at the turning point.  It also prints S at k = X - 1 for
X, 2X, and 4X, to show whether S increases with the argument.
"""
import sys
from decimal import Decimal as D, getcontext
import ordern as o

getcontext().prec = 200


def moduli(x, K):
    # the series of order 0 and 1 cancel to about x log10(e) digits
    getcontext().prec = max(200, int(0.44 * float(x)) + 80)
    J, Y = o.tables(x, K)
    return [J[k] * J[k] + Y[k] * Y[k] for k in range(K + 1)]


for arg in sys.argv[1:]:
    X = int(arg)
    x = D(X)
    M2 = moduli(x, X)
    smax = max((o.PI / 2 * (x * x - k * k).sqrt() * M2[k], k) for k in range(X))
    wmax = max((o.PI * x / 2 * M2[k], k) for k in range(X + 1))
    print(f"x={X}: max S={float(smax[0]):.10f} at k={smax[1]}, max weight={float(wmax[0]):.4f} "
          f"at k={wmax[1]}, x^(1/3)={X ** (1 / 3):.4f}, ratio={float(wmax[0]) / X ** (1 / 3):.4f}")
    k = X - 1
    vals = []
    for m in (1, 2, 4):
        xm = D(m * X)
        Mk = moduli(xm, k)[k]
        vals.append(float(o.PI / 2 * (xm * xm - k * k).sqrt() * Mk))
    print(f"   S at k={k} for x = {X}, {2 * X}, {4 * X}: {vals}")
