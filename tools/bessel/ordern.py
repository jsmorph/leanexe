# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Error propagation of the recurrences of `jn` and `yn`.

Usage: uv run tools/bessel/ordern.py

The program computes `J_k(x)` and `Y_k(x)` for `k ≤ 3x` to 200 digits: `J₀`, `J₁`, `Y₀`, and `Y₁`
from their series (DLMF 10.2.2 and 10.8.1), `Y_k` by forward recurrence (10.6.1), and `J_k` by
backward recurrence normalized by `J₀` or `J₁`.  It prints the cross product
`(π x/2)(J_(k+1) Y_k - J_k Y_(k+1))` (DLMF 10.5.2), the weight `(π x/2) M_k²` of the propagation
bound, the sum `S_n = Σ_(k<n) (π x/2) M_k²`, the propagated rounding of the forward
recurrence with the exact kernel `(π x/2)(Y_k J_n - J_k Y_n)` in place of its bound `M_k M_n`, and
the relative error of the normalization of Miller's method by the larger of `j0 x` and `j1 x`.
"""
from decimal import Decimal as D, getcontext

getcontext().prec = 200


def arctan_inv(n):
    x = D(1) / n; x2 = x * x; s = D(0); t = x; k = 0
    while abs(t) > D(10) ** -210:
        s += t / (2 * k + 1) if k % 2 == 0 else -t / (2 * k + 1)
        t *= x2; k += 1
    return s


PI = 4 * (4 * arctan_inv(5) - arctan_inv(239))


def euler_gamma(n=60):
    # Brent and McMillan's algorithm B1: the error is below π e^(-4n)
    a = -D(n).ln(); b = D(1); u = a; v = b; k = 1
    while not (abs(b) < D(10) ** -210 * abs(v) and k > 4 * n):
        b = b * n * n / (k * k)
        a = (a * n * n / k + b) / k
        u += a; v += b; k += 1
    return u / v


GAMMA = euler_gamma()


def orders01(x):
    """(J₀, J₁, Y₀, Y₁) at x > 0 from the series."""
    z = x * x / 4
    a0 = D(1); a1 = D(1); H = D(0); k = 0
    A0 = A1 = C0 = C1 = D(0)
    while True:
        sg = -1 if k % 2 else 1
        Hn = H + D(1) / (k + 1)
        A0 += sg * a0; A1 += sg * a1
        C0 += -sg * H * a0; C1 += sg * (H + Hn) * a1
        k += 1
        a0 = a0 * z / (k * k); a1 = a1 * z / (k * (k + 1))
        H = Hn
        if a0 < D(10) ** -210 and k > 5:
            break
    L = (x / 2).ln() + GAMMA
    J0 = A0; J1 = x / 2 * A1
    Y0 = 2 / PI * (L * J0 + C0)
    Y1 = 2 / PI * L * J1 - 2 / (PI * x) - x / (2 * PI) * C1
    return J0, J1, Y0, Y1


def tables(x, K):
    J0, J1, Y0, Y1 = orders01(x)
    Y = [Y0, Y1]
    for k in range(1, K + 1):
        Y.append(2 * k / x * Y[-1] - Y[-2])
    N = K + int(x) + 60
    f = [D(0)] * (N + 2); f[N] = D(10) ** -100
    for k in range(N, 0, -1):
        f[k - 1] = 2 * k / x * f[k] - f[k + 1]
    s = J0 / f[0] if abs(J0) > abs(J1) else J1 / f[1]
    return [v * s for v in f[:K + 2]], Y


def propagated(J, Y, F, x, n):
    """Σ_k w_k (π x/2) |Y_k J_n - J_k Y_n| / M_n, with w_k bounding the rounding of step k."""
    Mn = (J[n] ** 2 + Y[n] ** 2).sqrt()
    s = D(0)
    for k in range(1, n):
        w = 2 * (2 * k / x) * abs(F[k]) + abs(F[k - 1]) + abs(F[k + 1])
        s += w * PI * x / 2 * abs(Y[k] * J[n] - J[k] * Y[n])
    return s / Mn


def main():
    for xi in (20, 100, 300):
        x = D(xi); K = 3 * xi
        J, Y = tables(x, K)
        cas = max(abs(PI * x / 2 * (J[k + 1] * Y[k] - J[k] * Y[k + 1]) - 1) for k in range(K))
        wt = [PI * x / 2 * (J[k] ** 2 + Y[k] ** 2) for k in range(K + 1)]
        S = sum(wt[:xi])
        print('x = %d: cross product within %.1e of 1' % (xi, cas))
        for k in (xi // 2, 3 * xi // 4):
            print('  k = %d: (pi x/2) M_k^2 = %.4f, x/sqrt(x^2 - k^2) = %.4f'
                  % (k, wt[k], x / (x * x - k * k).sqrt()))
        print('  S_x / x = %.3f, (pi x/2) M_x^2 / x^(1/3) = %.3f'
              % (S / x, wt[xi] / x ** (D(1) / 3)))
        for n in (xi // 2, xi):
            print('  jn forward, n = %d: propagated rounding %.2f n u' % (n, propagated(J, Y, J, x, n) / n))
        for n in (xi // 2, xi, 3 * xi // 2, 2 * xi, K - 1):
            print('  yn forward, n = %d: propagated rounding %.2f n u' % (n, propagated(J, Y, Y, x, n) / n))
    worst = (D(0), D(0))
    for i in range(2000):
        x = D(2) + D(i) / 10
        J0, J1, Y0, Y1 = orders01(x)
        if abs(J0) >= abs(J1):
            r = 10 * (J0 * J0 + Y0 * Y0).sqrt() / abs(J0)
        else:
            r = 12 * (J1 * J1 + Y1 * Y1).sqrt() / abs(J1)
        worst = max(worst, (r, x))
    print('normalization: 10 M0/|J0| or 12 M1/|J1|, the larger of |J0| and |J1|, at most %.2f'
          ' on x = 2, 2.1, ..., 201.9 (at x = %s)' % (worst[0], worst[1]))


if __name__ == '__main__':
    main()
