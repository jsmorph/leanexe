# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks Demos.Gate.Assignment.check against an independent model of its rules and against the
least cost of each instance.

The least cost over the permutations through allowed pairs comes from enumerating the
permutations for n <= 9 and from dynamic programming over the subsets of columns for n = 16.  The
model of the check follows the requirements: three passes, the first failure in the order of the
passes and of the index, with its status, row, and column.

Each line of the input, which `verified-cases-assignment --bits` prints, holds
`check label n c perm u v status row col`, with each array as comma-separated words.  Every
result must equal the model's.  Every accepted assignment must have the least cost, which must
equal the sum of the certificate's values.  The solver's certificate of an instance with an
admissible assignment must be accepted, and that of an instance without one must give status 3.
Each mutation must be rejected, and the script reports the statuses of each label.
Usage: uv run tests/gate/assignment.py CASES"""
import itertools
import sys
from collections import Counter, defaultdict

MARK = 2**63 - 1
LIMIT = 2**62

# Mutations that make every certificate invalid: a raised dual value breaks the tightness of row
# 0, and the others give a value out of range, a column out of range, a forbidden pair of the
# assignment, a repeated column, a repeated column whose row stays tight, or a violated dual
# inequality, and the special cases of the same kinds.  A swap of two columns, or a dual
# value raised in one row and lowered in another, can give another optimal certificate.
INVALID = {"raised", "range", "column", "forbidden", "repeated", "tight-repeated", "violated",
           "duplicate", "order"}


def signed(w):
    w = int(w)
    return w - 2**64 if w >= 2**63 else w


def words(field):
    return [] if field == "" else [int(x) for x in field.split(",")]


def model(c, perm, u, v):
    n = len(perm)
    if not (1 <= n <= 16384 and len(c) == n * n and len(u) == n and len(v) == n):
        return (1, 0, 0)
    for i in range(n):
        if not (-LIMIT < u[i] < LIMIT and -LIMIT < v[i] < LIMIT):
            return (2, i, 0)
    for i in range(n):
        j = perm[i]
        if j >= n:
            return (3, i, j)
        w = c[i * n + j]
        if w == MARK:
            return (3, i, j)
        if u[i] + v[j] != w:
            return (5, i, j)
    for t in range(n * n):
        i, j = divmod(t, n)
        if i < j and perm[i] == perm[j]:
            return (3, j, perm[j])
        if c[t] < u[i] + v[j]:
            return (4, i, j)
    return (0, 0, 0)


def least(c, n):
    """The least cost of a permutation through allowed pairs, or None when there is none."""
    if n <= 9:
        best = None
        for p in itertools.permutations(range(n)):
            if any(c[i * n + p[i]] == MARK for i in range(n)):
                continue
            s = sum(c[i * n + p[i]] for i in range(n))
            if best is None or s < best:
                best = s
        return best
    if n <= 16:
        inf = None
        dp = {0: 0}
        for i in range(n):
            nxt = {}
            for mask, s in dp.items():
                for j in range(n):
                    if mask & (1 << j) or c[i * n + j] == MARK:
                        continue
                    m2 = mask | (1 << j)
                    t = s + c[i * n + j]
                    if m2 not in nxt or t < nxt[m2]:
                        nxt[m2] = t
            dp = nxt
        return dp.get((1 << n) - 1, inf)
    return shortest_paths(c, n)


def shortest_paths(c, n):
    """The least cost by successive shortest augmenting paths with the Bellman-Ford method on the
    residual graph, without potentials: an oracle independent of the Hungarian method."""
    INF = float("inf")
    match_row = [-1] * n
    match_col = [-1] * n
    for _ in range(n):
        # Nodes: 0..n-1 rows, n..2n-1 columns.  From a free row or along a row to a column at
        # cost c; from a matched column back to its row at cost -c.
        dist = [INF] * (2 * n)
        prev = [-1] * (2 * n)
        for i in range(n):
            if match_row[i] == -1:
                dist[i] = 0
        changed = True
        while changed:
            changed = False
            for i in range(n):
                if dist[i] == INF:
                    continue
                for j in range(n):
                    w = c[i * n + j]
                    if w == MARK or match_row[i] == j:
                        continue
                    if dist[i] + w < dist[n + j]:
                        dist[n + j] = dist[i] + w
                        prev[n + j] = i
                        changed = True
            for j in range(n):
                i = match_col[j]
                if i != -1 and dist[n + j] != INF and dist[n + j] - c[i * n + j] < dist[i]:
                    dist[i] = dist[n + j] - c[i * n + j]
                    prev[i] = n + j
                    changed = True
        free = [j for j in range(n) if match_col[j] == -1 and dist[n + j] != INF]
        if not free:
            return None
        j = min(free, key=lambda q: dist[n + q])
        node = n + j
        while True:
            i = prev[node]
            col = node - n
            match_col[col] = i
            old = match_row[i]
            match_row[i] = col
            if old == -1 or prev[i] == -1:
                break
            node = prev[i]
    return sum(c[i * n + match_row[i]] for i in range(n))


def main(path):
    failures = 0
    checks = 0
    statuses = defaultdict(Counter)
    for line in open(path):
        parts = line.split(" ")
        label, n = parts[1], int(parts[2])
        c = [signed(w) for w in words(parts[3])]
        perm = words(parts[4])
        u = [signed(w) for w in words(parts[5])]
        v = [signed(w) for w in words(parts[6])]
        result = (int(parts[7]), int(parts[8]), int(parts[9]))
        checks += 1
        statuses[label][result[0]] += 1
        expected = model(c, perm, u, v)
        if result != expected:
            print(f"fail {label} n={n}: result {result}, model {expected}")
            failures += 1
            continue
        if label in ("empty", "sizes"):
            continue
        opt = least(c, n) if n * n == len(c) else "unknown"
        if result[0] == 0:
            cost = sum(c[i * n + perm[i]] for i in range(n))
            if cost != sum(u) + sum(v):
                print(f"fail {label} n={n}: cost {cost} differs from the dual value {sum(u) + sum(v)}")
                failures += 1
            if opt != "unknown" and cost != opt:
                print(f"fail {label} n={n}: accepted cost {cost}, least cost {opt}")
                failures += 1
        if label == "solver":
            want = 3 if opt is None else 0
            if opt == "unknown":
                want = result[0] if result[0] in (0, 3) else 0
            if result[0] != want:
                print(f"fail solver n={n}: status {result[0]}, expected {want}")
                failures += 1
        elif label in INVALID and result[0] == 0:
            print(f"fail {label} n={n}: an invalid certificate was accepted")
            failures += 1
    for label in sorted(statuses):
        counts = ", ".join(f"status {s}: {k}" for s, k in sorted(statuses[label].items()))
        print(f"{label}: {counts}")
    print(f"{checks} checks, {failures} failures")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
