# /// script
# requires-python = ">=3.12"
# dependencies = ["mpmath==1.3.0"]
# ///
"""The comparison of the conjunction program with the two-dimensional unit tests of NASA's CARA
Analysis Tools, https://github.com/nasa/CARA_Analysis_Tools, at commit COMMIT.

The tools are under the NASA Open Source Agreement 1.3, whose section 3A requires that any
redistributed part of the software remain under that agreement with a copy of it.  The repository
therefore holds none of their numbers.  `fetch DIR` downloads the files of FILES from the commit
into DIR, `build/conjunction/cara` in tests/conjunction/cara.sh, and requires each file's size and
SHA-256 to equal those of FILES: a file already present with them is kept, and a download that
differs stays beside its target with the suffix `.mismatch` and fails the command.

CASES names, for each case, the unit test and the variables that hold its inputs and the expected
value of each of CARA's functions, with the tolerance with which the test compares the function's
result.  `inputs DIR` reads the inputs from the files, after checking their digests, and prints the
lines that `verified-cases-adaptive --evaluate` reads, as tests/conjunction/benchmark.py does.  An
inline input is a MATLAB matrix of the test's source.  A message input is a CDM of
DataFiles/SampleCDMs, which CARA's Pc_ObjectSetup.m reads: the state in EME2000 in km and km/s,
and the RTN covariance in m^2, rotated into the inertial frame with the axes R = r/|r|,
C = (r x v)/|r x v|, and I = C x R of RIC2ECI.m.  The test's own changes to these inputs, such as
the second position set to the first, follow the test.  When the relative position is shorter than
1e-6 HBR, PcCircle.m adds 1e-6 HBR (r1 + r2) x v/(|r1 + r2| |v|) to it, and so does this script.

The projection is that of benchmark.py with the mean at (|r|, 0), the full length of the relative
position, as CARA's functions place it.  For each case whose relative velocity is not zero, whose
projected covariance is positive definite at 50 digits, and whose radius is positive and finite,
the reference is that of benchmark.py, every result must have status 0 and contain it, and each
CARA value is compared with it at the test's tolerance, relative or absolute.  A value farther
away is a disagreement, which must have a recorded cause.  Every other case has no reference: its
results must have status 1, and CARA's value, 0 or NaN by CARA's conventions, has a recorded
cause.  `check DIR RESULTS` prints the report and exits with status 1 on a failure.
Usage: uv run tests/conjunction/cara.py fetch DIR | inputs DIR | check DIR RESULTS"""
import hashlib
import re
import sys
import time
import urllib.request
from decimal import Decimal
from pathlib import Path
from typing import NamedTuple

from mpmath import inf, mp, mpf, sqrt

import benchmark
import reference

COMMIT = '43f0160f94d76a91805d86521c3e8fa0d09ecd68'
BASE = f'https://raw.githubusercontent.com/nasa/CARA_Analysis_Tools/{COMMIT}/'
TESTS = 'DistributedMatlab/ProbabilityOfCollision/UnitTests/'
CDMS = 'DataFiles/SampleCDMs/'
FILES = {
    TESTS + 'Pc2D_Foster_UnitTest.m':
        (7629, 'fa8ae1dbdbc31f76a30c72856356e281d8871fcaed4d48592b8ecf04113d2970'),
    TESTS + 'PcCircle_UnitTest.m':
        (25625, '47b18026043aaadfbce6563d52b6a7d428ec94b890b097ac98204e017414fc53'),
    TESTS + 'PcElrod_UnitTest.m':
        (19202, '246d685e7e6b6736f0bef2ca4ca06ec011ac96979591ebed08361de00d21cd59'),
    TESTS + 'PcCircleWithConjData_UnitTest.m':
        (9143, 'ade986d8b8293362842e26e56bfc2af9e1387ad2587f00db353b8f4e0f75a827'),
    CDMS + 'AlfanoTestCase01.cdm':
        (10077, '1dab2db35266a7c91e4b67165c09ba45d2d4c1b54f3601be5dd1d040e2c3ab19'),
    CDMS + 'AlfanoTestCase02.cdm':
        (10076, 'c534f65d4b0f4fc6566232366b2b990f13350266111336cc87a981b12a0339e3'),
    CDMS + 'AlfanoTestCase03.cdm':
        (10077, '549a87adb6b64130e07d9b6b50b66e24155bdc036470f4218e98170d7081e199'),
    CDMS + 'AlfanoTestCase04.cdm':
        (10077, '4d0b36b968d645c908b229f0efa01f4f77aabc98b875facb31fedddf9eccc12c'),
    CDMS + 'AlfanoTestCase05.cdm':
        (10077, 'cdf3a4c7544341fc50a554638aa552e17d5a2b724b6fe57be256cf36a5d0b3c6'),
    CDMS + 'AlfanoTestCase06.cdm':
        (10077, '803eea780282fda98e3efa64cd298b801c7e7761497573e0ac71386c43c7d69f'),
    CDMS + 'OmitronTestCase_Test07_NonPDCovariance.cdm':
        (10096, 'ddb62be74ceaa06f385f1e36b0704ac9b6d3c69ddf7b2acbaf489e2d9b77a4bf'),
}

mp.dps = 50


class Inline(NamedTuple):
    """Inputs in the test file `file`, in the function `function` or, for None, in the properties
    block, under the names of r1 v1 cov1 r2 v2 cov2 HBR.  `row` selects a row of a vectorized
    input or of a vector HBR, `scale` multiplies the positions and velocities, and `same` sets
    `r2 = r1` or `v2 = v1`."""
    file: str
    function: str | None
    names: str
    row: int = 0
    scale: int = 1
    same: str | None = None


class Message(NamedTuple):
    """Inputs from the CDM `cdm` and the radius `hbr`, with `scale` and `same` as for Inline."""
    cdm: str
    hbr: str
    scale: int = 1
    same: str | None = None


class Expected(NamedTuple):
    """The value of CARA's function `label`, the variable `name` in the function `function` of the
    test file `file` at `row`, compared with tolerance `tol` relative or, with `absolute`,
    absolute.  `cause` records the cause of a disagreement or of a case without a reference."""
    label: str
    file: str
    function: str | None
    name: str
    tol: str
    row: int = 0
    absolute: bool = False
    cause: str | None = None


class Case(NamedTuple):
    name: str
    inputs: Inline | Message
    values: list[Expected]


FOSTER = TESTS + 'Pc2D_Foster_UnitTest.m'
CIRCLE = TESTS + 'PcCircle_UnitTest.m'
ELROD = TESTS + 'PcElrod_UnitTest.m'
CONJ = TESTS + 'PcCircleWithConjData_UnitTest.m'
LOCAL = 'r1 v1 cov1 r2 v2 cov2 HBR'
SWEEP_DOMAIN = ('CARA defines the probability as 0 for a radius of 0 and as 1 for an infinite '
                'radius, and the program rejects a radius that is not positive and finite.')
ZERO_VELOCITY = ('The relative velocity is zero, so no encounter plane exists, and PcCircle '
                 'returns NaN.  The program cannot be called.')


def zero_miss(i, same):
    return Case(f'PcCircle zero miss and velocity {i}', Message(f'AlfanoTestCase0{i}.cdm', '0.010',
                same=same),
                [Expected('PcCircle', CIRCLE, 'testZeroMissRelVelSingly', 'expSolution', '1e-10',
                          row=i, cause=ZERO_VELOCITY if same == 'v' else None)])


CASES = [
    Case('Omitron 1, Pc2D_Foster', Inline(FOSTER, None, 'r1 v1 cov1 r2 v2 cov2 OmitronHBR'),
         [Expected('Pc2D_Foster', FOSTER, 'testCircularHBR', 'expSolution', '1e-3')]),
    Case('Omitron 1, PcElrod', Inline(ELROD, 'testOmitronCase1', LOCAL),
         [Expected('PcElrod', ELROD, 'testOmitronCase1', 'expSolution', '1e-3')]),
    Case('Omitron 1, PcCircle',
         Inline(CIRCLE, None, 'omitronR1 omitronV1 omitronCov1 omitronR2 omitronV2 omitronCov2 '
                'omitronHBR'),
         [Expected('PcCircle, 64 points', CIRCLE, 'testOmitronCase1a', 'expSolution', '1e-10'),
          Expected('PcCircle, integral', CIRCLE, 'testOmitronCase1b', 'expSolution', '1e-10')]),
    Case('Omitron 2, PcCircle', Inline(CIRCLE, 'testOmitronCase2', 'r1 v1 cov1 r2 v2 cov2 HBR'),
         [Expected('PcCircle', CIRCLE, 'testOmitronCase2', 'expSolution', '1e-10')]),
    Case('Omitron 2, PcElrod', Inline(ELROD, 'testOmitronCase2', LOCAL),
         [Expected('PcElrod', ELROD, 'testOmitronCase2', 'expSolution', '1e-3')]),
    Case('Elrod similar to 3D', Inline(ELROD, 'testSimilarTo3D', LOCAL),
         [Expected('PcElrod', ELROD, 'testSimilarTo3D', 'expSolution', '1e-3')]),
    *[Case(f'HBR sweep {k}', Inline(CIRCLE, 'testMultipleElements', 'r1 v1 c1 r2 v2 c2 HBR', row=k),
           [Expected('PcCircle', CIRCLE, 'testMultipleElements', 'expSolution', '1e-10', row=k,
                     cause={0: SWEEP_DOMAIN, 7: SWEEP_DOMAIN, 1: 'ROUNDING', 2: 'ROUNDING'}.get(
                         k, 'QUADRATURE'))])
      for k in range(8)],
    *[Case(f'PcCircleWithConjData {k}',
           Inline(CONJ, None, 'multiR1 multiV1 multiCov1 multiR2 multiV2 multiCov2 multiHBR',
                  row=k),
           [Expected('PcCircleWithConjData', CONJ, None, 'multiPc', '1e-9', row=k,
                     cause='NPD' if k == 0 else 'ROUNDING')])
      for k in range(2)],
    Case('PcCircle NPD', Inline(CIRCLE, 'testNPDCovariance', LOCAL),
         [Expected('PcCircle', CIRCLE, 'testNPDCovariance', 'expSolution', '1e-10',
                   cause='NPD')]),
    Case('PcElrod NPD', Inline(ELROD, 'testNonPositiveDefinite', LOCAL),
         [Expected('PcElrod', ELROD, 'testNonPositiveDefinite', 'expSolution', '1e-3',
                   cause='NPD')]),
    Case('PcElrod NPD without remediation', Inline(ELROD, 'testNPDNoRemediation', LOCAL),
         [Expected('PcElrod', ELROD, 'testNPDNoRemediation', 'expSolution', '1e-3',
                   cause='NPD')]),
    Case('Omitron 7, message', Message('OmitronTestCase_Test07_NonPDCovariance.cdm', '20',
                                       scale=1000),
         [Expected('Pc2D_Foster', FOSTER, 'testNonPositiveDefinite', 'expSolution', '1e-10',
                   absolute=True, cause='NPD')]),
    zero_miss(1, None),
    zero_miss(2, 'r'),
    zero_miss(3, 'v'),
    zero_miss(4, 'r'),
    zero_miss(5, 'v'),
    zero_miss(6, None),
]


def digest(path: Path):
    data = path.read_bytes()
    return len(data), hashlib.sha256(data).hexdigest()


def fetch(root: Path) -> int:
    failures = 0
    for name, expected in FILES.items():
        target = root / name
        if target.exists() and digest(target) == expected:
            continue
        target.parent.mkdir(parents=True, exist_ok=True)
        request = urllib.request.Request(BASE + name, headers={'User-Agent': 'leanexe cara.py'})
        with urllib.request.urlopen(request, timeout=300) as response:
            data = response.read()
        got = len(data), hashlib.sha256(data).hexdigest()
        if got != expected:
            target.with_name(target.name + '.mismatch').write_bytes(data)
            print(f'mismatch: {name}: size {got[0]} SHA-256 {got[1]}, expected size {expected[0]} '
                  f'SHA-256 {expected[1]}')
            failures += 1
            continue
        target.write_bytes(data)
        time.sleep(1)
    print(f'{len(FILES) - failures} files of commit {COMMIT} in {root}, {failures} mismatched')
    return 1 if failures else 0


def read(root: Path, name: str) -> str:
    path = root / name
    if digest(path) != FILES[name]:
        raise SystemExit(f'{path}: size or SHA-256 differs from FILES; run fetch')
    return path.read_text()


def block(text: str, function: str | None) -> str:
    """The source of a test function, or of the properties block for None."""
    start = (text.index('properties (TestParameter)') if function is None
             else re.search(rf'function {function}\s*\(', text).start())
    end = re.compile(r'\n\s*(function |methods)').search(text, start + 1)
    return text[start:end.start() if end else len(text)]


def number(token: str):
    """The value of a MATLAB number, with None for NaN."""
    if token == 'NaN':
        return None
    if token in ('Inf', '-Inf'):
        return inf if token == 'Inf' else -inf
    return mpf(str(Decimal(token)))


def variable(source: str, name: str):
    """The rows of the MATLAB matrix or scalar assigned to `name` in `source`, as lists of mpf,
    after a trailing `.*FACTOR`.  A cell `{...}` around the value is dropped."""
    m = re.search(rf'(?m)^\s*{name}\s*=\s*\{{?', source)
    if m is None:
        raise SystemExit(f'no assignment of {name}')
    i = m.end()
    if source[i] != '[':
        scalar = re.match(r'[-+0-9.eE]+|Inf|NaN', source[i:])
        return [[number(scalar.group())]]
    depth, j = 0, i
    while True:
        depth += {'[': 1, ']': -1}.get(source[j], 0)
        j += 1
        if depth == 0:
            break
    body = re.sub(r'%[^\n]*', '', source[i + 1:j - 1])
    body = re.sub(r'\.\.\.[^\n]*\n', ' ', body)
    rows = [[number(t) for t in re.split(r'[\s,]+', row.strip())]
            for row in re.split(r'[;\n]', body) if row.strip()]
    factor = re.match(r"'?\s*\.\*\s*([-+0-9.eE]+)", source[j:])
    if factor:
        rows = [[x * mpf(factor.group(1)) for x in row] for row in rows]
    return rows


def matrix3(rows, row):
    """The 3x3 position block of a 3x3 or 6x6 matrix, or of row `row` of a vectorized input
    whose rows hold the nine entries in MATLAB's column order."""
    if len(rows) in (3, 6) and len(rows[0]) in (3, 6):
        return [r[:3] for r in rows[:3]]
    flat = rows[row]
    return [[flat[3 * j + i] for j in range(3)] for i in range(3)]


def vector(rows, row):
    return rows[row] if len(rows) > 1 and len(rows[0]) == 3 else rows[0]


def cdm(text: str):
    """The two objects' fields of a CDM in KVN, as dictionaries of mpf."""
    objects = []
    for line in text.splitlines():
        m = re.match(r'\s*([A-Z_]+)\s*=\s*(\S+)', line)
        if not m:
            continue
        key, value = m.groups()
        if key == 'OBJECT':
            objects.append({})
        elif objects and re.fullmatch(r'[-+0-9.eE]+', value):
            objects[-1][key] = mpf(value)
        elif objects:
            objects[-1][key] = value
    return objects


def message_state(obj):
    if obj['REF_FRAME'] != 'EME2000':
        raise SystemExit(f'frame {obj["REF_FRAME"]}')
    r = [obj['X'], obj['Y'], obj['Z']]
    v = [obj['X_DOT'], obj['Y_DOT'], obj['Z_DOT']]
    rtn = [[obj['CR_R'], obj['CT_R'], obj['CN_R']],
           [obj['CT_R'], obj['CT_T'], obj['CN_T']],
           [obj['CN_R'], obj['CN_T'], obj['CN_N']]]
    rhat = benchmark.unit(r)
    chat = benchmark.unit(benchmark.cross(r, v))
    ihat = benchmark.cross(chat, rhat)
    q = [[rhat[i], ihat[i], chat[i]] for i in range(3)]
    c = [[sum(q[i][a] * rtn[a][b] * q[j][b] for a in range(3) for b in range(3))
          for j in range(3)] for i in range(3)]
    return r, v, c


def states(root: Path, case: Case):
    """r1, v1, C1, r2, v2, C2, and HBR of a case, at 50 digits."""
    spec = case.inputs
    if isinstance(spec, Inline):
        source = block(read(root, spec.file), spec.function)
        names = spec.names.split()
        r1, v1, r2, v2 = (vector(variable(source, names[k]), spec.row) for k in (0, 1, 3, 4))
        c1, c2 = (matrix3(variable(source, names[k]), spec.row) for k in (2, 5))
        hbr = variable(source, names[6])
        hbr = hbr[spec.row][0] if len(hbr) > 1 else (hbr[0][spec.row] if len(hbr[0]) > 1
                                                       else hbr[0][0])
    else:
        first, second = cdm(read(root, CDMS + spec.cdm))
        r1, v1, c1 = message_state(first)
        r2, v2, c2 = message_state(second)
        hbr = mpf(spec.hbr)
    r1, v1, r2, v2 = ([x * spec.scale for x in w] for w in (r1, v1, r2, v2))
    if spec.same == 'r':
        r2 = r1
    if spec.same == 'v':
        v2 = v1
    return r1, v1, c1, r2, v2, c2, hbr


def plane(root: Path, case: Case):
    """The doubles (m1, m2, c11, c12, c22, r) of a case's encounter plane in CARA's convention,
    the mean of the in-plane convention, and None for each when the case has no plane."""
    r1, v1, c1, r2, v2, c2, hbr = states(root, case)
    r = [a - b for a, b in zip(r1, r2)]
    v = [a - b for a, b in zip(v1, v2)]
    if all(x == 0 for x in v):
        return None, None
    rmag = sqrt(benchmark.dot(r, r))
    if hbr < inf and rmag < mpf('1e-6') * hbr:
        s = [a + b for a, b in zip(r1, r2)]
        scale = mpf('1e-6') * hbr / (sqrt(benchmark.dot(s, s)) * sqrt(benchmark.dot(v, v)))
        r = [a + scale * b for a, b in zip(r, benchmark.cross(s, v))]
    c = [[c1[i][j] + c2[i][j] for j in range(3)] for i in range(3)]
    full = benchmark.encounter(r, v, c, full=True)
    inplane = benchmark.encounter(r, v, c)
    return tuple(float(x) for x in (*full, hbr)), inplane[0]


def value(root: Path, e: Expected):
    rows = variable(block(read(root, e.file), e.function), e.name)
    flat = [x for row in rows for x in row]
    return flat[e.row]


def tolerance(e: Expected, v):
    return mpf(e.tol) if e.absolute else mpf(e.tol) * abs(v)


def accepted(p) -> bool:
    m1, m2, c11, c12, c22, r = [mpf(x) for x in p]
    return c11 > 0 and c11 * c22 - c12 * c12 > 0 and 0 < r < inf


def inputs(root: Path):
    for case in CASES:
        p, _ = plane(root, case)
        if p is None:
            continue
        name = case.name.replace(' ', '-').replace(',', '')
        for method, n in benchmark.PANELS:
            print(method, name, *(benchmark.bits(x) for x in p), n)


def check(root: Path, path: str) -> int:
    results = {}
    for line in open(path):
        fields = line.split()
        if fields:
            results.setdefault(fields[1], []).append(fields)
    failures = 0
    computed = {}
    for case in CASES:
        name = case.name.replace(' ', '-').replace(',', '')
        p, inplane = plane(root, case)
        print(f'{case.name}')
        if p is None:
            print('  no encounter plane: the relative velocity is zero')
        else:
            print(f'  m=({p[0]!r}, {p[1]!r}) C=({p[2]!r}, {p[3]!r}, {p[4]!r}) r={p[5]!r}')
        ref = None
        if p is not None and accepted(p):
            if p not in computed:
                args = [mpf(x) for x in p]
                computed[p] = reference.reference(*args), benchmark.one_dimensional(*args)
            ref, other = computed[p]
            moved = benchmark.one_dimensional(inplane, *[mpf(x) for x in p[1:]])
            print(f'  reference {mp.nstr(ref, 20)}, one-dimensional form differs by '
                  f'{mp.nstr(abs(other - ref) / ref, 3)}, the in-plane mean changes it by '
                  f'{mp.nstr((moved - other) / other, 3)}')
            if abs(other - ref) > benchmark.AGREEMENT * ref:
                print('  FAIL the two reference quadratures disagree')
                failures += 1
        for e in case.values:
            v = value(root, e)
            shown = 'NaN' if v is None else mp.nstr(v, 17)
            if ref is None or v is None or v in (inf, -inf):
                agrees = False
                print(f'  {e.label} {shown}: no reference')
            else:
                agrees = abs(v - ref) <= tolerance(e, v)
                difference = mp.nstr((v - ref) / ref, 3)
                kind = 'absolute' if e.absolute else 'relative'
                print(f'  {e.label} {shown}: relative difference {difference}, '
                      f'{"agrees" if agrees else "disagrees"} at {kind} {e.tol}')
            if not agrees and e.cause is None:
                print('  FAIL disagreement without a recorded cause')
                failures += 1
            elif agrees and e.cause is not None:
                print('  FAIL a cause is recorded but the value agrees')
                failures += 1
            elif e.cause is not None:
                print(f'    cause: {CAUSES.get(e.cause, e.cause)}')
                if ref is not None and v is not None and not evidence(e.cause, p, v, ref):
                    print('  FAIL the computation does not support the recorded cause')
                    failures += 1
        got = results.get(name, [])
        expected = 0 if p is None else len(benchmark.PANELS)
        if len(got) != expected:
            print(f'  FAIL {len(got)} results, {expected} expected')
            failures += 1
        for fields in got:
            method, n, status = fields[0], int(fields[8]), int(fields[9])
            lo, hi = mpf(benchmark.double(fields[10])), mpf(benchmark.double(fields[11]))
            ok = (status == 0 and lo <= ref <= hi) if ref is not None else status == 1
            failures += not ok
            width = mp.nstr((hi - lo) / ref, 3) if ref else '-'
            marks = ', '.join(
                f'{e.label} {benchmark.relation(lo, hi, v, tolerance(e, v))}'
                for e in case.values if ref is not None
                for v in [value(root, e)] if v is not None)
            print(f'  {"ok  " if ok else "FAIL"} {method} n={n} status={status} '
                  f'lo={mp.nstr(lo, 17)} hi={mp.nstr(hi, 17)} relative width {width}; {marks}')
    print(f'{failures} failures')
    return 1 if failures else 0


CAUSES = {
    'NPD': 'CARA clips the eigenvalues of the projected covariance below (1e-4 HBR)^2 and returns '
           '0, or NaN without that remediation, and the program, which applies no remediation, '
           'rejects the covariance.',
    'QUADRATURE': 'PcCircle integrates over the disk with a 64-point Gauss-Chebyshev rule, and '
                  'the same rule in exact arithmetic differs from the reference by the same '
                  'amount.  The radius spans 54 to 1,609 standard deviations of the minor axis.',
    'ROUNDING': 'The 64-point rule agrees with the reference in exact arithmetic, so the '
                'difference comes from rounding.  PcCircle computes the smaller eigenvalue of '
                'the projected covariance, 348 m^2, as (T - sqrt(T^2 - 4 D))/2 in binary64 with '
                'the trace T = 1.5e10 m^2, which leaves an error of up to 2^-53 T, and the '
                'probability with the eigenvalue moved by that error differs from the reference '
                'by more than CARA\'s value does.',
}


def principal(p):
    """The eigenvalues L1 >= L2 of the plane covariance of `p` and the mean's coordinates
    along their eigenvectors, at 50 digits."""
    m1, _, c11, c12, c22, _ = [mpf(x) for x in p]
    half = sqrt(((c11 - c22) / 2) ** 2 + c12 * c12)
    l1 = (c11 + c22) / 2 + half
    l2 = (c11 * c22 - c12 * c12) / l1
    if c12 != 0:
        u = benchmark.unit([l1 - c22, c12, mpf(0)])
    else:
        u = [mpf(1), mpf(0)] if c11 >= c22 else [mpf(0), mpf(1)]
    return l1, l2, abs(m1 * u[0]), abs(m1 * u[1])


def gauss_chebyshev(p, n=64):
    """The probability of `p` by PcCircle's rule: in the covariance's principal axes, the
    integral over the major coordinate x of the normal density of x times the probability of the
    disk's chord at x along the minor axis, with the n-point Gauss-Chebyshev rule of the second
    kind over [xm - r, xm + r], at 50 digits."""
    l1, l2, xm, zm = principal(p)
    r = mpf(p[5])
    sx, sz = sqrt(l1), sqrt(l2)
    total = mpf(0)
    for k in range(1, n + 1):
        t = k * mp.pi / (n + 1)
        x, h = xm - r * mp.cos(t), r * mp.sin(t)
        chord = (mp.erf((zm + h) / (sz * sqrt(2))) - mp.erf((zm - h) / (sz * sqrt(2)))) / 2
        total += mp.sin(t) * mp.npdf(x, 0, sx) * chord
    return r * mp.pi / (n + 1) * total


def rounding_bound(p):
    """The change of the probability of `p` when its smaller eigenvalue moves by 2^-53 times the
    trace."""
    l1, l2, xm, zm = principal(p)
    r = mpf(p[5])
    shift = mpf(2) ** -53 * (l1 + l2)
    base = benchmark.one_dimensional(xm, zm, l1, mpf(0), l2, r)
    return abs(benchmark.one_dimensional(xm, zm, l1, mpf(0), l2 + shift, r) - base)


def evidence(cause, p, v, ref) -> bool:
    """Prints the computation behind a cause and whether it holds."""
    if cause == 'QUADRATURE':
        g = gauss_chebyshev(p)
        ok = abs(g - v) <= mpf('1e-6') * abs(v)
        print(f'    64-point rule at 50 digits: relative difference {mp.nstr((g - ref) / ref, 3)} '
              f'from the reference, {mp.nstr((g - v) / v, 3)} from CARA\'s value')
        return ok
    if cause == 'ROUNDING':
        g, bound = gauss_chebyshev(p), rounding_bound(p)
        ok = abs(g - ref) <= mpf('1e-20') * ref and abs(v - ref) <= bound
        print(f'    64-point rule at 50 digits: relative difference {mp.nstr((g - ref) / ref, 3)}; '
              f'the eigenvalue moved by 2^-53 T moves the probability by '
              f'{mp.nstr(bound / ref, 3)} of it')
        return ok
    return True


def main() -> int:
    if len(sys.argv) == 3 and sys.argv[1] == 'fetch':
        return fetch(Path(sys.argv[2]))
    if len(sys.argv) == 3 and sys.argv[1] == 'inputs':
        inputs(Path(sys.argv[2]))
        return 0
    if len(sys.argv) == 4 and sys.argv[1] == 'check':
        return check(Path(sys.argv[2]), sys.argv[3])
    print(__doc__.rsplit('\n', 1)[-1], file=sys.stderr)
    return 2


if __name__ == '__main__':
    sys.exit(main())
