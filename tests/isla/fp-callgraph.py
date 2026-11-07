# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Checks, over the call graph of Isla's IR, the readings on which the abstract floating-point calls
of the traces of tests/isla rest.  The traces of the floating-point forms leave FPAdd64, FPSub64,
FPMul64, FPDiv64, FPSqrt64, FixedToFP64, and FPToFixed64 abstract
(tests/isla/armv9p4-checked-fp.diff), and FPCompare, whose result has 4 bits at every width, and a
theorem of tests/TestSupport/A64/Isla takes as a hypothesis that each call returns the reference
interpreter's function of its arguments.  That reading needs the original functions FPAdd, FPSub,
FPMul, FPDiv, FPSqrt, FixedToFP, and FPToFixed, which the wrappers call, and FPCompare to return
without a Sail exception, to compute their result from their arguments and from registers that the
configuration fixes and the instruction does not change, and to write no register but FPSR, which
the theorems list among the registers that a form changes.

For each function, the script follows the statements that the function's entry reaches, and the
functions that those statements call, without the edges of PRUNED and the branches that KNOWN
rules out.  Each removed edge is a branch that the startup's FPCR, 0x02000000, the processor's
AArch64 state at EL1, or the pseudocode itself rules out:
  * FPProcessException tests the trap enable of the exception, FPCR bit 8 + k for the kinds
    InvalidOp, DivideByZero, Overflow, Underflow, Inexact, and InputDenorm (k = 0, 1, 2, 3, 4, 7),
    and its trap branch, which also reads PSTATE.SM and SMCR_ELx and enters the exception, runs
    only when that bit is set (v8_base.sail 15601);
  * FPRoundBase reads FPCR.UFE for a trapped underflow, and its test of PSTATE.SM and of
    FEAT_SME_FA64 runs only when UFE is set (v8_base.sail 15713);
  * the default cases of FPRoundBase's two matches on the rounding mode leave its variables
    round_up and overflow_to_inf undefined, and only FPRounding_TIEAWAY reaches them, which
    FPRoundBase's assertion at its entry excludes (v8_base.sail 15647);
  * the default case of FPToFixed's match on the rounding mode leaves its variable round_up
    undefined, and only FPRounding_ODD reaches it, which FPToFixed's assertion at its entry
    excludes (v8_base.sail 17847);
  * the default case of FPDecodeRounding returns an undefined mode, and no 2-bit RMode reaches it;
  * UsingAArch32() is false at EL1 with PSTATE.nRW 0, so the branches that write FPSCR, which
    holds FPCR and FPSR, do not run.
The script prints each removed edge with its statement and fails if the statement is not a jump to
the edge's target.  It then checks that (a) no statement reached sets have_exception and no
function reached calls itself through the graph; (b) the registers read are FeatureImpl, which the
profile fixes, PSTATE.nRW, which is 0 at EL1 in AArch64 state, and FPSR, and every value read from
FPSR flows only into a write of FPSR; (c) no register is written but FPSR; and (d) no variable is
used on a path from a statement that makes it undefined, an `undefined_*` primitive or
`internal_pick`, without an assignment between, where a copy passes the undefined value on.  It
prints the loops of the functions reached, whose termination it does not check: the normalization
loops of FPRoundBase, which run while a finite nonzero real lies outside [1, 2) (v8_base.sail 15684
and 15688).

Usage: uv run tests/isla/fp-callgraph.py IR, where IR is armv9p4-checked-fp.ir.  The script prints
a summary for each function and exits with status 1 if a check fails.
"""

import re
import sys

ROOTS = ['zFPAdd', 'zFPSub', 'zFPMul', 'zFPDiv', 'zFPSqrt', 'zFixedToFP', 'zFPToFixed',
         'zFPCompare']

# (function, statement index of a jump, target, reason): the edges that the docstring lists.
PRUNED = [
    ('zFPProcessException', 78, 81, 'FPCR trap enable of the exception is clear'),
    ('zFPProcessException', 106, 148, 'FPCR trap enable of the exception is clear'),
    ('zFPRoundBase__1', 436, 439, 'FPCR.UFE is clear'),
    ('zFPRoundBase__1', 592, 599, 'the rounding mode is not FPRounding_TIEAWAY'),
    ('zFPRoundBase__1', 765, 775, 'the rounding mode is not FPRounding_TIEAWAY'),
    ('zFPDecodeRounding', 48, 50, 'RMode has two bits, of which the four cases cover every value'),
    ('zFPToFixed', 244, 268, 'the rounding mode is not FPRounding_ODD'),
]

# Functions of no arguments whose result is known: a jump on a variable that one of them sets
# takes only the branch of that result.
KNOWN = {'zUsingAArch32': False}

ALLOWED_READS = {'zFeatureImpl', 'zPSTATE.znRW', 'zFPSR', 'zFPSR.zbits'}
ALLOWED_WRITES = {'zFPSR'}
UNDEFINED = re.compile(r'undefined|internal_pick')


def parse(path):
    fns, regs, prims = {}, set(), {}
    cur = None
    with open(path) as f:
        for line in f:
            if cur is not None:
                if line.startswith('}'):
                    fns[cur[0]] = (cur[1], cur[2])
                    cur = None
                else:
                    cur[2].append(line.strip().split(' `')[0].rstrip(';').strip())
                continue
            if line.startswith('fn '):
                m = re.match(r'fn (\S+?)\((.*)\) \{', line)
                cur = [m.group(1), [a.strip() for a in m.group(2).split(',') if a.strip()], []]
            elif line.startswith('register '):
                regs.add(line.split()[1])
            else:
                m = re.match(r'(?:val|abstract) (\S+) = "([^"]*)"', line)
                if m:
                    prims[m.group(1)] = m.group(2)
    return fns, regs, prims


def succs(stmts, i):
    s = stmts[i]
    m = re.match(r'jump .* goto (\d+)$', s)
    if m:
        return [i + 1, int(m.group(1))]
    m = re.match(r'goto (\d+)$', s)
    if m:
        return [int(m.group(1))]
    if s in ('end', 'arbitrary') or s.startswith('exit'):
        return []
    return [i + 1]


def known_edges(name, stmts):
    vals, out = {}, set()
    for s in stmts:
        m = re.match(r'(\S+) = (z[A-Za-z0-9_]+)\(\(\)\)$', s)
        if m and m.group(2) in KNOWN:
            vals[m.group(1)] = KNOWN[m.group(2)]
    for i, s in enumerate(stmts):
        m = re.match(r'jump (@not\()?(\S+?)\)? goto (\d+)$', s)
        if m and m.group(2) in vals:
            taken = vals[m.group(2)] != bool(m.group(1))
            out.add((i, i + 1) if taken else (i, int(m.group(3))))
    return out


def tokens(text):
    return re.findall(r'\$?z[A-Za-z0-9_]*(?:\.z[A-Za-z0-9_]*)*\(?', text)


def split(s):
    """The assigned name and the text that the statement reads."""
    m = re.match(r'([A-Za-z0-9_.$]+) = (.*)$', s)
    if m and m.group(1) not in ('have_exception', 'current_exception', 'throw_location'):
        return m.group(1), m.group(2)
    m = re.match(r'jump (.*) goto \d+$', s)
    if m:
        return None, m.group(1)
    if re.match(r'\S+ : ', s) or re.match(r'goto \d+$', s) or s in ('end', 'arbitrary'):
        return None, ''
    return None, s


def check(path):
    fns, regs, prims = parse(path)
    pruned = {}
    failed = False
    for f, i, j, why in PRUNED:
        pruned.setdefault(f, set()).add((i, j))
        stmt = fns[f][1][i]
        print(f'removed: {f[1:]} {i} -> {j}, {why}: {stmt}')
        if not re.match(rf'jump .* goto {j}$', stmt):
            print(f'  FAIL the statement is not a jump to {j}')
            failed = True
    for root in ROOTS:
        todo, seen, calls = [root], set(), {}
        reads, writes, throws, undef, taint, loops = {}, {}, [], [], [], set()
        while todo:
            fn = todo.pop()
            if fn in seen:
                continue
            seen.add(fn)
            params, stmts = fns[fn]
            decls = (re.match(r'(\S+) : ', s) for s in stmts)
            locs = set(params) | {m.group(1) for m in decls if m}
            cut = pruned.get(fn, set()) | known_edges(fn, stmts)
            live, stack = set(), [0]
            while stack:
                i = stack.pop()
                if i in live or i >= len(stmts):
                    continue
                live.add(i)
                stack += [j for j in succs(stmts, i) if (i, j) not in cut]
            calls[fn] = set()
            for i in sorted(live):
                s = stmts[i]
                if s == 'have_exception = true':
                    throws.append((fn, i))
                for j in succs(stmts, i):
                    if j <= i and (i, j) not in cut and s.startswith(('goto', 'jump')):
                        loops.add(fn)
                lhs, rhs = split(s)
                if lhs and lhs.split('.')[0] in regs and lhs.split('.')[0] not in locs:
                    writes.setdefault(lhs, set()).add(fn)
                for t in tokens(rhs):
                    name = t.rstrip('(').split('.')[0]
                    if t.endswith('('):
                        if name in fns:
                            calls[fn].add(name)
                            todo.append(name)
                    elif name in regs and name not in locs:
                        reads.setdefault(t, set()).add(fn)
            undef += undefined_uses(fn, stmts, locs, cut, fns, prims)
            taint += fpsr_flows(fn, stmts, locs, live, fns)
        cycle = find_cycle(calls)
        bad_reads = sorted(r for r in reads if r not in ALLOWED_READS)
        bad_writes = sorted(w for w in writes if w not in ALLOWED_WRITES)
        print(f'{root[1:]}: {len(seen)} functions reached')
        print('  reads:', ', '.join(f'{r[1:]} ({" ".join(sorted(f[1:] for f in reads[r]))})'
                                    for r in sorted(reads)))
        print('  writes:', ', '.join(f'{w[1:]} ({" ".join(sorted(f[1:] for f in writes[w]))})'
                                     for w in sorted(writes)))
        print('  loops in:', ' '.join(sorted(f[1:] for f in loops)) or 'none')
        for name, bad in [('throw reached', throws), ('recursion', [cycle] if cycle else []),
                          ('read outside the allowed registers', bad_reads),
                          ('write outside FPSR', bad_writes),
                          ('use of an undefined value', sorted(set(map(str, undef)))),
                          ('value read from FPSR flows elsewhere', taint)]:
            if bad:
                failed = True
                print(f'  FAIL {name}: {bad[:10]}')
        if not failed:
            print('  checks (a) to (d) hold')
    return failed


def undefined_uses(fn, stmts, locs, cut, fns, prims):
    """Uses of a variable that a path from an undefined value reaches without an assignment."""
    def source(rhs):
        m = re.match(r'(\$?z[A-Za-z0-9_]+)\(', rhs)
        if not m:
            return False
        f = m.group(1)
        return (f in prims and UNDEFINED.match(prims[f])) or f.startswith('zundefined_')
    state = {0: frozenset()}
    order = [0]
    bad = []
    while order:
        i = order.pop()
        if i >= len(stmts):
            continue
        cur = state[i]
        lhs, rhs = split(stmts[i])
        copy = lhs in locs and rhs in locs
        used = {t.rstrip('(') for t in tokens(rhs) if not t.endswith('(')}
        used = {u.split('.')[0] for u in used if u.split('.')[0] in locs}
        hit = used & cur
        if hit and not copy:
            bad.append((fn[1:], i, sorted(hit)))
        out = set(cur)
        if lhs:
            base = lhs.split('.')[0]
            if base in locs and '.' not in lhs:
                if source(rhs) or (copy and rhs in cur):
                    out.add(base)
                else:
                    out.discard(base)
        for j in succs(stmts, i):
            if (i, j) in cut:
                continue
            new = state.get(j, frozenset()) | out
            if j not in state or new != state[j]:
                state[j] = frozenset(new)
                order.append(j)
    return bad


def fpsr_flows(fn, stmts, locs, live, fns):
    """Statements through which a value read from FPSR reaches anything but a write of FPSR: a
    jump, a call of an IR function, a return, or a write of another register."""
    tainted, bad = set(), []
    for i in sorted(live):
        lhs, rhs = split(stmts[i])
        toks = [t for t in tokens(rhs)]
        bases = {t.rstrip('(').split('.')[0] for t in toks if not t.endswith('(')}
        if 'zFPSR' not in bases and not bases & tainted:
            continue
        base = lhs.split('.')[0] if lhs else None
        called = {t.rstrip('(') for t in toks if t.endswith('(')} & set(fns)
        if base == 'zFPSR' and not called:
            continue
        if base in locs and not called:
            tainted.add(base)
            continue
        bad.append((fn[1:], i))
    return bad


def find_cycle(calls):
    state = {}

    def visit(f, path):
        state[f] = 1
        for g in sorted(calls.get(f, ())):
            if state.get(g) == 1:
                return path[path.index(g):] + [g]
            if g not in state:
                c = visit(g, path + [g])
                if c:
                    return c
        state[f] = 2
        return None
    for f in sorted(calls):
        if f not in state:
            c = visit(f, [f])
            if c:
                return c
    return None


if __name__ == '__main__':
    sys.exit(1 if check(sys.argv[1]) else 0)
