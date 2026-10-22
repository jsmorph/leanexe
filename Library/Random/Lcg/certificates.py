# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Certificates for the spectral test of the LCG of Examples/Lcg/Program.lean.

For t = 2, ..., 6 the script reduces the canonical basis C of the dual lattice
{s : s_0 + s_1 a + ... + s_(t-1) a^(t-1) = 0 (mod 2^64)} with exact LLL, finds the shortest vector
by Fincke-Pohst enumeration, and prints the Lean definitions and theorems of the certificates in
Library/Random/Lcg/Spectral.lean: the reduced basis B, the matrix U with U B = C, the adjugate A with
B A = delta I, the box bounds b with (nu^2 - 1) sum_k A_ki^2 < (b_i + 1)^2 delta^2, and nu^2.  The
kernel checks every certificate, so the theorems do not depend on this script.  Run with
`uv run Library/Random/Lcg/certificates.py`.
"""
from fractions import Fraction
import math

M = 2**64
A_MULT = 6364136223846793005


def dot(u, v):
    return sum(x * y for x, y in zip(u, v))


def gram_schmidt(B):
    n = len(B)
    star, mu = [], [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        v = [Fraction(x) for x in B[i]]
        for j in range(i):
            mu[i][j] = Fraction(dot(B[i], star[j])) / dot(star[j], star[j])
            v = [x - mu[i][j] * y for x, y in zip(v, star[j])]
        star.append(v)
    return star, mu


def lll(B, delta=Fraction(99, 100)):
    B = [list(b) for b in B]
    k = 1
    while k < len(B):
        star, mu = gram_schmidt(B)
        for j in range(k - 1, -1, -1):
            q = round(mu[k][j])
            if q:
                B[k] = [x - q * y for x, y in zip(B[k], B[j])]
                star, mu = gram_schmidt(B)
        if dot(star[k], star[k]) >= (delta - mu[k][k - 1] ** 2) * dot(star[k - 1], star[k - 1]):
            k += 1
        else:
            B[k], B[k - 1] = B[k - 1], B[k]
            k = max(k - 1, 1)
    return B


def canonical(t):
    """The canonical basis of the dual lattice in `t` dimensions, Lean's `canonical (t - 1)`."""
    rows = [[M] + [0] * (t - 1)]
    for k in range(1, t):
        row = [0] * t
        row[0] = -pow(A_MULT, k, M)
        row[k] = 1
        rows.append(row)
    return rows


def shortest(B):
    n = len(B)
    star, mu = gram_schmidt(B)
    norms = [dot(b, b) for b in star]
    best = min(dot(b, b) for b in B)
    bestv = min(B, key=lambda b: dot(b, b))

    def rec(i, z, partial):
        nonlocal best, bestv
        if i < 0:
            if any(z):
                v = [sum(z[j] * B[j][c] for j in range(n)) for c in range(n)]
                if dot(v, v) < best:
                    best, bestv = dot(v, v), v
            return
        c = -sum(mu[j][i] * z[j] for j in range(i + 1, n))
        r = (Fraction(best) - partial) / norms[i]
        if r < 0:
            return
        w = math.isqrt(int(r) + 1) + 1
        for zi in range(math.floor(c) - w, math.ceil(c) + w + 1):
            d = (zi - c) ** 2 * norms[i]
            if partial + d <= best:
                z[i] = zi
                rec(i - 1, z, partial + d)
        z[i] = 0

    rec(n - 1, [0] * n, Fraction(0))
    return best, bestv


def inverse(B):
    n = len(B)
    rows = [[Fraction(x) for x in row] + [Fraction(int(i == j)) for j in range(n)]
            for i, row in enumerate(B)]
    det = Fraction(1)
    for c in range(n):
        p = next(r for r in range(c, n) if rows[r][c] != 0)
        if p != c:
            rows[c], rows[p] = rows[p], rows[c]
            det = -det
        det *= rows[c][c]
        pivot = rows[c][c]
        rows[c] = [x / pivot for x in rows[c]]
        for r in range(n):
            if r != c and rows[r][c] != 0:
                f = rows[r][c]
                rows[r] = [x - f * y for x, y in zip(rows[r], rows[c])]
    return int(det), [row[n:] for row in rows]


def matmul(X, Y):
    return [[sum(X[i][k] * Y[k][j] for k in range(len(Y))) for j in range(len(Y[0]))]
            for i in range(len(X))]


def wrap(items, first, indent, width=100):
    """The items joined by ", " in lines of at most `width` characters, after the text `first`."""
    lines, line = [], first
    for k, item in enumerate(items):
        piece = item + (", " if k < len(items) - 1 else "")
        if len(line) + len(piece.rstrip()) > width and line.strip():
            lines.append(line.rstrip())
            line = indent
        line += piece
    lines.append(line.rstrip())
    return "\n".join(lines)


def lean_matrix(X):
    items = []
    for k, row in enumerate(X):
        cells = [str(x) for x in row]
        cells[-1] += ";" if k < len(X) - 1 else "]"
        items.extend(cells)
    out = wrap(items, "  !![", "    ")
    return out.replace(";, ", "; ").replace(";,", ";")


WORDS = {2: "two", 3: "three", 4: "four", 5: "five", 6: "six"}

for t in range(2, 7):
    C = canonical(t)
    B = lll(C)
    nu2, v = shortest(B)
    delta, inv = inverse(B)
    A = [[int(x * delta) for x in row] for row in inv]
    U = [[int(x) for x in row] for row in matmul(C, inv)]
    assert matmul(U, B) == C and matmul(B, A) == [[delta * int(i == j) for j in range(t)]
                                                  for i in range(t)]
    bounds = []
    for i in range(t):
        col = sum(A[k][i] ** 2 for k in range(t))
        b = 0
        while not ((nu2 - 1) * col < (b + 1) ** 2 * delta ** 2):
            b += 1
        bounds.append(b)
    print(f"/-- A reduced basis of `Dual {t}`. -/")
    print(f"def basis{t} : Matrix (Fin {t}) (Fin {t}) ℤ :=\n{lean_matrix(B)}")
    print(f"/-- The matrix whose product with `basis{t}` is `canonical {t - 1}`. -/")
    print(f"def unimodular{t} : Matrix (Fin {t}) (Fin {t}) ℤ :=\n{lean_matrix(U)}")
    print(f"/-- The adjugate of `basis{t}`. -/")
    print(f"def adjugate{t} : Matrix (Fin {t}) (Fin {t}) ℤ :=\n{lean_matrix(A)}")
    print(f"/-- The bounds of the box of coefficients for `t = {t}`. -/")
    print(f"def bounds{t} : Fin {t} → ℕ := ![{', '.join(map(str, bounds))}]")
    print(f"-- The shortest vector of `Dual {t}`, `shortest{t}` of Lattice.lean: "
          f"![{', '.join(map(str, v))}]")
    print()
    print(f"/-- The spectral test value `ν_{t}² = {nu2}`: every nonzero vector of `Dual {t}` has")
    print(f"squared length at least {nu2}, which `shortest{t}` attains. -/")
    print(f"theorem spectral_{WORDS[t]} :")
    print(f"    (∀ s : Fin {t} → ℤ, Dual {t} s → s ≠ 0 → {nu2} ≤ ∑ k, s k ^ 2) ∧")
    print(f"      Dual {t} shortest{t} ∧ ∑ k, shortest{t} k ^ 2 = {nu2} := by")
    print("  refine ⟨fun s hs h0 => ?_, by decide +kernel, by decide +kernel⟩")
    print(f"  obtain ⟨y, rfl⟩ := dual_eq_vecMul (t := {t - 1}) hs")
    print(f"  exact le_of_certificate (canonical {t - 1}) unimodular{t} basis{t} adjugate{t} "
          f"({delta})")
    print(f"    {nu2} bounds{t} (by decide +kernel) (by decide +kernel) (by decide +kernel)")
    print("    (by decide +kernel) y h0")
    print()
