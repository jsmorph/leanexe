# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Writes Project/Gpt/Composites.lean: the `Implements` theorems of the GPT functions
that call other compiled functions, hold their results as temporaries, and release
them at the end, proved with the `Live` invariant.  Each theorem comes from a
description of the function's calls.

Run with `uv run tools/gpt_composites.py`; with `--check`, it only reports whether the
file is up to date."""
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TARGET = ROOT / 'Project/Gpt/Composites.lean'


def wrap(s, ind, width=86):
    out, line = [], ''
    for part in s.split(', '):
        cand = (line + ', ' + part) if line else part
        if len(cand) > width and line:
            out.append(line + ',')
            line = part
        else:
            line = cand
    out.append(line)
    return ('\n' + ind).join(out)


def cap(n):
    return n[0].upper() + n[1:]


def ptr(n):
    return 'p' + cap(n)


def hyp(n):
    return 'h' + cap(n)


def mem(pos):
    m = 'List.mem_cons_self ..'
    for _ in range(pos):
        m = f'List.mem_cons_of_mem _ ({m})'
    return m


def arg_reads(a):
    if isinstance(a, tuple):
        if a[0] in ('mul', 'add'):
            return arg_reads(a[1]) + arg_reads(a[2])
        if a[0] == 'const':
            return []
        return [a[1]]
    return [a]


def represent(items, tail):
    """`items`: list of (pointer, proof) for the arrays of a tuple, in order; `tail`:
    whether scalars follow the arrays."""
    parts = []
    for idx, (p, src) in enumerate(items):
        inner = f'⟨{p}, rfl, {src}⟩'
        if not tail and idx == len(items) - 1:
            parts.append(inner)
        else:
            parts.append(f'[.i64 {p}], _, rfl, {inner}')
    if tail:
        parts.append('rfl')
    if len(items) == 1 and not tail:
        return parts[0]
    return '⟨' + ', '.join(parts) + '⟩'


def state_fact(r, states, i=None):
    """A proof that local `r` of `states[i]`, the last state by default, holds its
    value.  A state is `start`, the previous state with one local updated, or the
    state after a loop over an array, which frames the previous state."""
    if i is None:
        i = len(states) - 1
    e = states[i]
    if e['kind'] == 'start':
        return f'sg{r}'
    prev = states[i - 1]
    if e['kind'] == 'update':
        if e['reg'] == r:
            return f"State.get_update_same (state := {prev['name']}) (by rw [{prev['len']}]; decide)"
        return (f"(State.get_update_ne (state := {prev['name']}) (j := {r}) (index := {e['reg']}) "
                f"(by decide)).trans ({state_fact(r, states, i - 1)})")
    if e['reg'] == r:
        return e['fact']
    return f"({e['frame']}.get {r} (by decide) (by decide)).trans ({state_fact(r, states, i - 1)})"


def eval_term(e, fact):
    """A proof that the `u64` expression `e`, a local, a constant, a product, or a sum,
    evaluates; `fact(r)` proves that local `r` holds its value."""
    if isinstance(e, tuple):
        if e[0] == 'const':
            return 'Expr.eval_const'
        lemma = 'Expr.eval_mul' if e[0] == 'mul' else 'Expr.eval_add'
        return f'{lemma} ({eval_term(e[1], fact)}) ({eval_term(e[2], fact)})'
    return f'Expr.eval_get ({fact(e)})'


def value_term(e, names):
    """The value of the `u64` expression `e` in terms of the names of the locals."""
    if isinstance(e, tuple):
        if e[0] == 'const':
            return str(e[1])
        left = value_term(e[1], names)
        right = value_term(e[2], names)
        if e[0] == 'mul':
            if isinstance(e[1], tuple) and e[1][0] == 'add':
                left = f'({left})'
            if isinstance(e[2], tuple) and e[2][0] != 'const':
                right = f'({right})'
            return f'{left} * {right}'
        if isinstance(e[2], tuple) and e[2][0] == 'add':
            right = f'({right})'
        return f'{left} + {right}'
    return names[e]


def eval_lines(args, fact, ind):
    """The proof that the arguments evaluate, one line per argument."""
    out = []
    for a in args:
        if isinstance(a, tuple) and a[0] in ('mul', 'add'):
            out.append(f'Expr.evalResults_u64 ({eval_term(a, fact)}) <|')
        elif isinstance(a, tuple) and a[0] == 'f':
            out.append(f'Expr.evalResults_getF ({fact(a[1])}) <|')
        elif isinstance(a, tuple) and a[0] == 'const':
            out.append('Expr.evalResults_u64 rfl <|')
        else:
            out.append(f'Expr.evalResults_get ({fact(a)}) <|')
    out.append('Expr.evalResults_nil')
    out[0] = '(' + out[0]
    out[-1] = out[-1] + ')'
    return [ind + out[0]] + [ind + '  ' + line for line in out[1:]]


def composite(spec):
    temps_by_reg = {}
    regvals = {}        # values of locals that plain statements assign
    name = spec['name']
    params = spec['params']            # list of (name, kind): 'A', 'U', 'u', 'f'
    nparams = len(params)
    nlocals = spec['nlocals']
    width = spec.get('width', 0)
    total = nparams + nlocals + width
    names = [n for n, _ in params]
    calls = spec['calls']
    L = len(calls)
    loops = any(c.get('kind') == 'loop' for c in calls)
    lines = []
    if spec.get('heartbeats'):
        lines.append('set_option maxHeartbeats 1000000 in')
    lines.append(f"theorem {name}_implements : Implements gpt.module {spec['entry']} "
                 f"{spec['tuple']} := by")
    lines.append(f"  refine Func.implements_heap gpt.funcs {spec['index']} gpt.{name}.ir \"{name}\" rfl")
    lines.append(f"    {spec['tuple']}")
    # The arguments are taken apart one array at a time with `Represent.borrowed_float_pair`
    # and `Represent.borrowed_uint_pair`; `rintro` patterns on the undestructured tuple
    # grow with about the fourth power of the number of arrays.
    lemma = {'A': 'Represent.borrowed_float_pair', 'U': 'Represent.borrowed_uint_pair'}
    lines.append(f'    (by')
    lines.append(f'      rintro _ _ _ ⟨{wrap(", ".join("_" for _ in names), "        ")}⟩ h')
    for n, k in params:
        if k in 'AU':
            lines.append(f'      obtain ⟨_, _, rfl, -, h⟩ := {lemma[k]} h')
    lines.append('      obtain rfl := h')
    lines.append('      rfl) ?_')
    lines.append(f'  rintro ⟨{wrap(", ".join(names), "    ")}⟩ heap initial _ hHeap hArgs hCap')
    for n, k in params:
        if k in 'AU':
            lines.append(f'  obtain ⟨{ptr(n)}, _, rfl, {hyp(n)}, hArgs⟩ := {lemma[k]} hArgs')
    lines.append('  obtain rfl := hArgs')
    lines.append('  have hImports : gpt.module.imports = [] := rfl')
    lines.append('  have hRelease : gpt.module.funcs[1]? = some (releaseFunction 1) := rfl')
    if loops:
        lines.append('  have hMemory32 : gpt.module.memIs64 = false := rfl')
        lines.append('  have hAlloc : gpt.module.funcs[0]? = some (allocFunction 0) := rfl')
    if spec.get('one'):
        lines.append('  have hOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel')
    for hname, entry, index, ir in spec['funcs']:
        lines.append(f'  have {hname} : gpt.module.funcs[{entry} - gpt.module.imports.length]? =')
        lines.append(f'      some (gpt.{ir}.ir.function (2 + {index})) :=')
        lines.append(f'    compile_funcs (funcs := gpt.funcs) (i := {index}) rfl')
    for n, term in spec['lets']:
        lines.append(f'  let {n} := {wrap(term, "    ")}')
    for h in spec.get('haves', []):
        lines.append(h)
    vals = []
    for n, k in params:
        vals.append(f'.f64 {n}.toBits' if k == 'f' else (f'.i64 {n}' if k == 'u' else f'.i64 {ptr(n)}'))
    lines.append('  let start : State :=')
    lines.append(f'    {{ params := [{wrap(", ".join(vals), "        ")}]')
    lines.append(f'      locals := [{", ".join([".i64 0"] * (nlocals + width))}] }}')
    lines.append(f'  have hStart : start.params.length + start.locals.length = {total} := rfl')
    lines.append('  have hLen : ∀ (s : State) (j : Nat) (v : Value),')
    lines.append('      (s.update j v).params.length + (s.update j v).locals.length =')
    lines.append('        s.params.length + s.locals.length := fun s j v => by')
    lines.append('    simp [State.update_params_length, State.update_locals_length]')
    for j, v in enumerate(vals):
        lines.append(f'  have sg{j} : start.get {j} = some ({v}) := rfl')
    # The body stays named, and the kernel computes its scratch width: restating the
    # body, or computing the width in the elaborator, exceeds Lean's recursion depth
    # for the longer bodies.  Composite bodies need no scratch locals, apart from the
    # copy that starts a loop over an array, whose bounds need the scratch index.
    lines.append(f'  have hWidth : gpt.{name}.ir.width = {width} := by decide +kernel')
    if width == 0:
        lines.append('  simp only [Func.state, Func.locals, hWidth, List.replicate_zero, List.append_nil]')
    else:
        lines.append(f'  have hScratch : gpt.{name}.ir.scratch = {nparams + nlocals} := by decide +kernel')
        lines.append('  simp only [Func.state, Func.locals, hWidth, hScratch]')
    lines.append(f'  show Triple _ gpt.{name}.ir.body _')
    lines.append('    (fun store state => store = initial ∧ state = start) _')
    # The calls.
    live = '(Live.start hHeap)'
    states = [dict(kind='start', name='start', len='hStart')]
    chain = []          # the updated states, for `simp`
    temps = []          # newest first: pointers
    steps = []          # (register, pointer) of each call's result
    def fact(r):
        return state_fact(r, states)
    rnames = dict(enumerate(names))
    for n, c in enumerate(calls):
        k = n + 1
        cur = states[-1]
        lines.append(f"  -- {c['comment']}")
        if c.get('kind') == 'run':
            reg = c['reg']
            names_r = []
            for r in c['reads']:
                v = regvals[r] if r in regvals else vals[r]
                lines.append(f"  have f{k}_{r} : {cur['name']}.get {r} = some ({v}) :=")
                lines.append(f"    {fact(r)}")
                names_r.append(f'f{k}_{r}')
            # Scratch locals that the statement's expression writes, in order.
            prev = cur
            scratch_names = []
            for r, v in c.get('scratch', []):
                nm = f's{k}_{r}'
                lines.append(f"  let {nm} := {prev['name']}.update {r} (.i64 ({v}))")
                lines.append(f"  have h{nm} : {nm}.params.length + {nm}.locals.length = {total} := by rw [hLen, {prev['len']}]")
                states.append(dict(kind='update', name=nm, len=f'h{nm}', reg=r))
                prev = states[-1]
                scratch_names.append(nm)
            lines.append(f"  let s{k} := {prev['name']}.update {reg} (.i64 ({c['value']}))")
            lines.append(f"  have hS{k} : s{k}.params.length + s{k}.locals.length = {total} := by rw [hLen, {prev['len']}]")
            facts = ', '.join(names_r + scratch_names + [f's{k}'])
            lines.append(f"  refine Stmt.seq_spec (Stmt.run_spec (final := s{k}) (by")
            lines.append(f"    {c['proof'].format(facts=facts, cur=cur['name'], curlen=cur['len'], k=k)})) ?_")
            states.append(dict(kind='update', name=f's{k}', len=f'hS{k}', reg=reg))
            regvals[reg] = f".i64 ({c['value']})"
            rnames[reg] = f"({c['value']})"
            continue
        if c.get('kind') == 'loop':
            p = c['ptr']
            lines.append(f"  refine Live.arrayLoop {c['impl']} rfl {c['hfunc']} rfl hMemory32 hImports hAlloc")
            lines.append(f"    hRelease (by decide) (by decide) (by decide) (by decide) (by rw [{cur['len']}]; decide)")
            lines.append(f"    {live} hCap ({fact(c['src'])})")
            lines.append(f"    ({live}.tempsOwned _ ({mem(temps.index(c['init_ptr']))})).borrowed (init := {c['init']})")
            lines.append(f"    (fun _ st hF => ⟨_, Expr.eval_get ((hF.get {c['count']} (by decide) (by decide)).trans")
            lines.append(f"      ({fact(c['count'])}))⟩)")
            lines.append(f"    (fun l x => {wrap(c['F'], '      ')})")
            def inner(r):
                if r == c['state']:
                    return 'hSt'
                if r == c['index']:
                    return 'hI'
                return f"(hF.get {r} (by decide) (by decide)).trans ({fact(r)})"
            cvals = []
            for a in c['args']:
                if a == c['state']:
                    cvals.append('.i64 p')
                elif a == c['index']:
                    cvals.append('.i64 (UInt64.ofNat k)')
                elif isinstance(a, tuple) and a[0] == 'f':
                    cvals.append(vals[a[1]])
                elif isinstance(a, tuple):
                    cvals.append(f'.i64 ({value_term(a, rnames)})')
                elif a in regvals:
                    cvals.append(regvals[a])
                else:
                    cvals.append(vals[a])
            lines.append(f"    (fun k p _ _ st _ hF hI hSt hL =>")
            lines.append(f"      ⟨[{wrap(', '.join(cvals), '        ')}], st,")
            body = eval_lines(c['args'], inner, '        ')
            body[-1] += ','
            lines.extend(body)
            items = [('p', '(hL.tempsOwned _ (List.mem_cons_self ..)).borrowed')]
            items += [(ptr(a), f'hL.borrowed {ptr(a)} _ {hyp(a)} Apart.nil') for kind, a in c['borrowed']]
            lines.append(f"        {wrap(represent(items, True), '          ')}⟩)")
            lines.append(f"    fun heap{k} {p} store{k} s{k} hLive{k} hFrame{k} hState{k} => ?_")
            lines.append(f"  have hS{k} : s{k}.params.length + s{k}.locals.length = {total} := by")
            lines.append(f"    rw [hFrame{k}.params, hFrame{k}.locals]; exact {cur['len']}")
            states.append(dict(kind='frame', name=f's{k}', len=f'hS{k}', frame=f'hFrame{k}',
                               reg=c['state'], fact=f'hState{k}'))
            live = f'hLive{k}'
            temps.insert(0, p)
            temps_by_reg[c['state']] = p
            steps.append((c['state'], p))
            continue
        reg = c.get('reg', nparams + n)
        lines.append(f"  refine Live.call_seq {c['impl']} rfl {c['hfunc']} rfl {live} hCap")
        lines.append(f"    (x := {c['x']}) (afterArgs := {cur['name']})")
        cvals = []
        for a in c['args']:
            if isinstance(a, tuple) and a[0] in ('mul', 'add'):
                cvals.append(f'.i64 ({value_term(a, rnames)})')
            elif isinstance(a, tuple) and a[0] == 'f':
                cvals.append(vals[a[1]])
            elif isinstance(a, tuple) and a[0] == 'scale':
                cvals.append(spec['scaleval'])
            elif isinstance(a, tuple) and a[0] == 'const':
                cvals.append(f'.i64 {a[1]}')
            elif a in regvals:
                cvals.append(regvals[a])
            elif a >= nparams:
                cvals.append(f'.i64 {temps_by_reg[a]}')
            else:
                cvals.append(vals[a])
        lines.append(f'    (vals := [{wrap(", ".join(cvals), "      ")}])')
        reads = sorted({r for a in c['args'] for r in arg_reads(a)})
        if any(isinstance(a, tuple) and a[0] == 'scale' for a in c['args']):
            # The scale's floating-point operations need the `F64Bits` lemmas and the
            # default `simp` set.
            simp = ['Expr.evalResults', 'Expr.eval']
            simp += list(reversed(chain))
            if any(r >= nparams for r in reads):
                simp += ['State.get_update_same', 'hStart']
            simp += [f'sg{r}' for r in reads if r < nparams]
            simp += c.get('simp_extra', [])
            lines.append(f'    (by simp [{wrap(", ".join(simp), "      ")}])')
        else:
            # Each argument's value, from facts about the state; `simp` over the whole
            # argument list costs several seconds for the longer lists.
            lines.extend(eval_lines(c['args'], fact, '    '))
        items = []
        for kind, a in c['borrowed']:
            if kind == 'P':
                src = hyp(a) if live == '(Live.start hHeap)' else f'{live}.borrowed {ptr(a)} _ {hyp(a)} Apart.nil'
                items.append((ptr(a), src))
            else:
                items.append((a, f'({live}.tempsOwned _ ({mem(temps.index(a))})).borrowed'))
        lines.append(f"    {wrap(represent(items, c.get('tail', True)), '      ')}")
        p = c['ptr']
        lines.append(f"    (by rw [{cur['len']}]; decide) fun heap{k} {p} store{k} hLive{k} => ?_")
        lines.append(f"  let s{k} := {cur['name']}.update {reg} (.i64 {p})")
        lines.append(f"  have hS{k} : s{k}.params.length + s{k}.locals.length = {total} := by rw [hLen, {cur['len']}]")
        states.append(dict(kind='update', name=f's{k}', len=f'hS{k}', reg=reg))
        chain.append(f's{k}')
        live = f'hLive{k}'
        temps.insert(0, p)
        temps_by_reg[reg] = p
        steps.append((reg, p))
    # The result local and the releases.
    res = spec.get('result', nparams + L)
    last, before_last = states[-1], states[-2]
    sL = last['name']
    sR = f's{L + 1}'
    lines.append(f'  let {sR} := {sL}.update {res} (.i64 {calls[-1]["ptr"]})')
    lines.append(f'  refine Stmt.seq_spec (Stmt.run_spec (final := {sR}) (by')
    lines.append(f'    simp [Stmt.run, Expr.eval, State.set?_eq_update _ (show {res} < {sL}.params.length +')
    lines.append(f"      {sL}.locals.length by rw [{last['len']}]; decide), {sR}, {sL}, State.get_update_same,")
    lines.append(f"      show {last['reg']} < {before_last['name']}.params.length + {before_last['name']}.locals.length by rw [{before_last['len']}]; decide])) ?_")
    states.append(dict(kind='update', name=sR, len=None, reg=res))
    lines.append('  -- The temporaries are released, newest first.')
    for reg, p in steps[:-1]:
        lines.append(f'  have r{reg} : {sR}.get {reg} = some (.i64 {p}) :=')
        lines.append(f'    {fact(reg)}')
    regs = [reg for reg, _ in steps[:-1]][::-1]
    for idx, reg in enumerate(regs):
        rule = 'releaseSecond_seq' if idx < len(regs) - 1 else 'releaseSecond_last'
        lines.append(f'  refine {live}.{rule} hImports hRelease r{reg} fun storeR{idx} hLiveR{idx} => ?_')
        live = f'hLiveR{idx}'
    lines.append("  obtain ⟨heap', hAt', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=")
    lines.append(f"    {live}.finish")
    lines.append(f"  exact ⟨heap', hAt', hCaps', hKeepB, hKeepO, [.i64 {calls[-1]['ptr']}], {sR},")
    scratch = 'Func.scratch, ' if width == 0 else ''
    lines.append(f'    by simp [gpt.{name}.ir, {scratch}Expr.evalResults, Expr.eval, {sR},')
    lines.append(f"      State.get_update_same, {last['len']}], hOwned, hOutB, hOutO⟩")
    return '\n'.join(lines) + '\n'


def proj(n, k):
    return 'x' + '.2' * k + ('' if k == n - 1 else '.1')


def tuple_type(kinds):
    m = {'A': 'Array Float', 'U': 'Array UInt64', 'u': 'UInt64', 'f': 'Float'}
    return wrap(' × '.join(m[k] for k in kinds).replace(' × ', ', '), '    ', 80).replace(', ', ' × ').replace(',\n', ' ×\n')


def tuple_def(name, fn, params, doc):
    kinds = [k for _, k in params]
    n = len(params)
    ps = ' '.join(proj(n, k) for k in range(n))
    return (f'/-- {doc} -/\n'
            f'def {name} (x : {tuple_type(kinds)}) : Array Float :=\n'
            f'  LeanExe.Examples.Gpt.{fn} {wrap(ps.replace(" ", ", "), "    ", 80).replace(", ", " ").replace(",", "")}\n')


# ------------------------------------------------------------------ mlp
MLP = [('x', 'A'), ('wfc', 'A'), ('bfc', 'A'), ('wproj', 'A'), ('bproj', 'A'), ('l', 'u'), ('t', 'u'),
       ('d', 'u'), ('f', 'u')]
mlp_spec = dict(
    name='mlp', entry=13, index=11, tuple='mlpTuple', params=MLP, nlocals=4,
    funcs=[('hLinear', 29, 27, 'linear'), ('hGelu', 12, 10, 'geluArray')],
    lets=[('h', 'linearTuple (x, wfc, bfc, l, t, d, f)'), ('g', 'LeanExe.Examples.Gpt.geluArray h')],
    calls=[
        dict(args=[0, 1, 2, 5, 6, 7, 8], impl='linear_implements', hfunc='hLinear',
             x='(x, wfc, bfc, l, t, d, f)',
             borrowed=[('P', 'x'), ('P', 'wfc'), ('P', 'bfc')], ptr='ph', comment='`h = x · wfc + bfc`.'),
        dict(args=[9], impl='geluArray_implements', hfunc='hGelu', x='h', borrowed=[('T', 'ph')], tail=False, ptr='pg',
             comment='`g = gelu h`.'),
        dict(args=[10, 3, 4, 5, 6, 8, 7], impl='linear_implements', hfunc='hLinear',
             x='(g, wproj, bproj, l, t, f, d)',
             borrowed=[('T', 'pg'), ('P', 'wproj'), ('P', 'bproj')], ptr='pr',
             comment='The result, `g · wproj + bproj`.'),
    ])
mlp_section = tuple_def('mlpTuple', 'mlp', MLP, '`mlp` with its nine arguments as one tuple.') + f'''
''' + composite(mlp_spec) + '\n'

# ------------------------------------------------------------------ attention
ATT = [(n, 'A') for n in ['x', 'wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo']] + [('l', 'u'), ('t', 'u'), ('nh', 'u'),
                                                                                ('dh', 'u')]
lin_calls = []
for idx, (w, b, ptrname, reg) in enumerate([('wq', 'bq', 'pq', 1), ('wk', 'bk', 'pk', 3), ('wv', 'bv', 'pv', 5)]):
    lin_calls.append(dict(args=[0, reg, reg + 1, 9, 10, ('mul', 11, 12), ('mul', 11, 12)],
                          impl='linear_implements', hfunc='hLinear', x=f'(x, {w}, {b}, l, t, nh * dh, nh * dh)', borrowed=[('P', 'x'), ('P', w), ('P', b)], ptr=ptrname,
                          comment=f'`{ptrname[1]} = x · {w} + {b}`.'))
att_spec = dict(
    name='attention', entry=23, index=21, tuple='attentionTuple', params=ATT,
    nlocals=8, one=True,
    funcs=[('hLinear', 29, 27, 'linear'), ('hMasked', 18, 16, 'maskedScores'),
           ('hSoftmax', 22, 20, 'softmaxRows'), ('hCausal', 25, 23, 'causalMatMul')],
    lets=[('q', 'linearTuple (x, wq, bq, l, t, nh * dh, nh * dh)'),
          ('k', 'linearTuple (x, wk, bk, l, t, nh * dh, nh * dh)'),
          ('v', 'linearTuple (x, wv, bv, l, t, nh * dh, nh * dh)'),
          ('s', 'maskedTuple (q, k, t, nh, dh, 1.0 / dh.toFloat.sqrt)'),
          ('p', 'softmaxRowsTuple (s, t, nh)'),
          ('o', 'causalMatMulTuple (p, v, t, nh, dh)')], scaleval='.f64 (1.0 / dh.toFloat.sqrt).toBits',
    calls=lin_calls + [
        dict(args=[13, 14, 10, 11, 12, ('scale', 12)], impl='maskedScores_implements',
             hfunc='hMasked', x='(q, k, t, nh, dh, 1.0 / dh.toFloat.sqrt)',
             borrowed=[('T', 'pq'), ('T', 'pk')], ptr='ps',
             simp_extra=['F64Op.apply', 'F64UnOp.apply', 'F64Bits.toBits_div', 'F64Bits.toBits_sqrt',
                         'F64Convert.toBits_toFloat', 'hOne'],
             comment='The masked scores of `q` and `k`, head by head.'),
        dict(args=[16, 10, 11], impl='softmaxRows_implements', hfunc='hSoftmax',
             x='(s, t, nh)',
             borrowed=[('T', 'ps')], ptr='pp', comment='The softmax of each of the `t · nh` rows of scores.'),
        dict(args=[17, 15, 10, 11, 12], impl='causalMatMul_implements', hfunc='hCausal',
             x='(p, v, t, nh, dh)', borrowed=[('T', 'pp'), ('T', 'pv')], ptr='po',
             comment='`o = p · v`, row `i` summing over rows `0` to `i` of `v`.'),
        dict(args=[18, 7, 8, 9, 10, ('mul', 11, 12), ('mul', 11, 12)], impl='linear_implements',
             hfunc='hLinear', x='(o, wo, bo, l, t, nh * dh, nh * dh)',
             borrowed=[('T', 'po'), ('P', 'wo'), ('P', 'bo')], ptr='pr', comment='The result, `o · wo + bo`.'),
    ])
att_section = tuple_def('attentionTuple', 'attention', ATT, '`attention` with its thirteen arguments as one tuple.') + '''
''' + composite(att_spec) + '\n'

# ------------------------------------------------------------------ block
BARR = ['x', 'g1', 'b1', 'wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo', 'g2', 'b2', 'wfc', 'bfc', 'wproj', 'bproj']
BLK = [(n, 'A') for n in BARR] + [('l', 'u'), ('t', 'u'), ('nh', 'u'), ('dh', 'u'), ('f', 'u'), ('eps', 'f')]
blk_spec = dict(
    name='block', entry=24, index=22, tuple='blockTuple', params=BLK, nlocals=7,
    funcs=[('hNorm', 17, 15, 'layerNormRows'), ('hAttention', 23, 21, 'attention'), ('hAdd', 9, 7, 'add'),
           ('hMlp', 13, 11, 'mlp')],
    lets=[('h1', 'layerNormRowsTuple (x, g1, b1, l, t, nh * dh, eps)'),
          ('a', 'attentionTuple (h1, wq, bq, wk, bk, wv, bv, wo, bo, l, t, nh, dh)'),
          ('r', 'addTuple (x, a)'),
          ('h2', 'layerNormRowsTuple (r, g2, b2, l, t, nh * dh, eps)'),
          ('m', 'mlpTuple (h2, wfc, bfc, wproj, bproj, l, t, nh * dh, f)')],
    calls=[
        dict(args=[0, 1, 2, 17, 18, ('mul', 19, 20), ('f', 22)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(x, g1, b1, l, t, nh * dh, eps)',
             borrowed=[('P', 'x'), ('P', 'g1'), ('P', 'b1')], ptr='ph1', comment='The first layer norm.'),
        dict(args=[23, 3, 4, 5, 6, 7, 8, 9, 10, 17, 18, 19, 20], impl='attention_implements',
             hfunc='hAttention', x='(h1, wq, bq, wk, bk, wv, bv, wo, bo, l, t, nh, dh)',
             borrowed=[('T', 'ph1')] + [('P', n) for n in ['wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo']],
             ptr='pa', comment='Attention.'),
        dict(args=[0, 24], impl='add_implements', hfunc='hAdd', x='(x, a)',
             borrowed=[('P', 'x'), ('T', 'pa')], tail=False, ptr='pr',
             comment='The first residual sum, `r = x + a`.'),
        dict(args=[25, 11, 12, 17, 18, ('mul', 19, 20), ('f', 22)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(r, g2, b2, l, t, nh * dh, eps)',
             borrowed=[('T', 'pr'), ('P', 'g2'), ('P', 'b2')], ptr='ph2', comment='The second layer norm.'),
        dict(args=[26, 13, 14, 15, 16, 17, 18, ('mul', 19, 20), 21], impl='mlp_implements', hfunc='hMlp',
             x='(h2, wfc, bfc, wproj, bproj, l, t, nh * dh, f)',
             borrowed=[('T', 'ph2'), ('P', 'wfc'), ('P', 'bfc'), ('P', 'wproj'), ('P', 'bproj')], ptr='pm',
             comment='The MLP.'),
        dict(args=[25, 27], impl='add_implements', hfunc='hAdd', x='(r, m)',
             borrowed=[('T', 'pr'), ('T', 'pm')], tail=False, ptr='pres', comment='The result, `r + m`.'),
    ])
BT = tuple_type([k for _, k in BLK])
blk_section = tuple_def('blockTuple', 'block', BLK, '`block` with its twenty-three arguments as one tuple.') + f'''
''' + composite(blk_spec) + '\n'

# ------------------------------------------------------------------ forward
LAYER = BARR[1:]
FWD = ([('tokens', 'U'), ('wte', 'A'), ('wpe', 'A')] + [(n, 'A') for n in LAYER] +
       [('gf', 'A'), ('bf', 'A'), ('layers', 'u'), ('t', 'u'), ('nh', 'u'), ('dh', 'u'), ('f', 'u'),
        ('vocab', 'u'), ('eps', 'f')])
FWD_NAMES = [n for n, _ in FWD]
LAYER_F = '(x, ' + ', '.join(LAYER) + ', l, t, nh, dh, f, eps)'
fwd_spec = dict(
    name='forward', entry=28, index=26, tuple='forwardTuple', params=FWD,
    nlocals=9, width=1, result=36,
    funcs=[('hEmbed', 26, 24, 'embed'), ('hBlock', 24, 22, 'block'),
           ('hNorm', 17, 15, 'layerNormRows'), ('hScores', 27, 25, 'matMulT')],
    lets=[('x0', 'embedTuple (tokens, wte, wpe, t, nh * dh)'),
          ('xl', f'LeanExe.loop layers x0 fun l x => blockTuple {LAYER_F}'),
          ('h', 'layerNormRowsTuple (xl, gf, bf, 0, t, nh * dh, eps)')],
    calls=[
        dict(args=[0, 1, 2, 22, ('mul', 23, 24)], impl='embed_implements', hfunc='hEmbed', reg=28,
             x='(tokens, wte, wpe, t, nh * dh)',
             borrowed=[('P', 'tokens'), ('P', 'wte'), ('P', 'wpe')], ptr='px0', comment='The embeddings.'),
        dict(kind='loop', impl='block_implements', hfunc='hBlock', state=29, index=32, src=28,
             init='x0', init_ptr='px0', count=21,
             args=[29] + list(range(3, 19)) + [32, 22, 23, 24, 25, ('f', 27)], F=LAYER_F,
             borrowed=[('P', n) for n in LAYER], ptr='pl', comment='The blocks, one per layer.'),
        dict(args=[29, 19, 20, ('const', 0), 22, ('mul', 23, 24), ('f', 27)],
             impl='layerNormRows_implements', hfunc='hNorm', reg=34, x='(xl, gf, bf, 0, t, nh * dh, eps)', borrowed=[('T', 'pl'), ('P', 'gf'), ('P', 'bf')],
             ptr='ph', comment='The final layer norm.'),
        dict(args=[34, 1, 22, ('mul', 23, 24), 26], impl='matMulT_implements', hfunc='hScores', reg=35,
             x='(h, wte, t, nh * dh, vocab)',
             borrowed=[('T', 'ph'), ('P', 'wte')], ptr='pr',
             comment='The scores against every token embedding.'),
    ])
FT = tuple_type([k for _, k in FWD])
pat = ', '.join(FWD_NAMES)
fwd_section = f"""/-- The input of `forward`: the tokens, the embeddings, the stacked weights of the blocks,
the final layer norm, and the dimensions. -/
abbrev ForwardInput := {FT}

/-- `forward` with its twenty-eight arguments as one tuple. -/
def forwardTuple : ForwardInput → Array Float
  | ({wrap(pat, '     ')}) =>
    LeanExe.Examples.Gpt.forward {wrap(' '.join(FWD_NAMES).replace(' ', ', '), '      ', 80).replace(', ', ' ').replace(',', '')}

""" + composite(fwd_spec) + '\n'


# ------------------------------------------------------------------ layerStep
LSA = ['s', 'cache'] + BARR[1:]
LS = [(n, 'A') for n in LSA] + [('l', 'u'), ('p', 'u'), ('nh', 'u'), ('dh', 'u'), ('f', 'u'),
                                ('bsize', 'u'), ('eps', 'f')]
LD = ('mul', 20, 21)
ONE = ('const', 1)
ls_spec = dict(
    name='layerStep', entry=40, index=38, tuple='layerStepTuple', params=LS,
    nlocals=15, one=True,
    funcs=[('hFirst', 31, 29, 'firstRow'), ('hNorm', 17, 15, 'layerNormRows'),
           ('hLinear', 29, 27, 'linear'), ('hScores', 32, 30, 'stepScores'),
           ('hSoftmax', 35, 33, 'stepSoftmax'), ('hMix', 36, 34, 'stepMix'), ('hAdd', 9, 7, 'add'),
           ('hMlp', 13, 11, 'mlp'), ('hWrite', 37, 35, 'writeBlock')],
    lets=[('x', 'firstRowTuple (s, nh * dh)'),
          ('h1', 'layerNormRowsTuple (x, g1, b1, l, 1, nh * dh, eps)'),
          ('q', 'linearTuple (h1, wq, bq, l, 1, nh * dh, nh * dh)'),
          ('k', 'linearTuple (h1, wk, bk, l, 1, nh * dh, nh * dh)'),
          ('v', 'linearTuple (h1, wv, bv, l, 1, nh * dh, nh * dh)'),
          ('sc', 'stepScoresTuple (q, k, cache, l, p, nh, dh, bsize, 1.0 / dh.toFloat.sqrt)'),
          ('pw', 'stepSoftmaxTuple (sc, nh, p + 1)'),
          ('o', 'stepMixTuple (pw, v, cache, l, p, nh, dh, bsize)'),
          ('a', 'linearTuple (o, wo, bo, l, 1, nh * dh, nh * dh)'),
          ('r', 'addTuple (x, a)'),
          ('h2', 'layerNormRowsTuple (r, g2, b2, l, 1, nh * dh, eps)'),
          ('m', 'mlpTuple (h2, wfc, bfc, wproj, bproj, l, 1, nh * dh, f)'),
          ('y', 'addTuple (r, m)')],
    scaleval='.f64 (1.0 / dh.toFloat.sqrt).toBits',
    calls=[
        dict(args=[0, LD], impl='firstRow_implements', hfunc='hFirst', x='(s, nh * dh)', borrowed=[('P', 's')], ptr='px', comment='The hidden row.'),
        dict(args=[25, 2, 3, 18, ONE, LD, ('f', 24)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(x, g1, b1, l, 1, nh * dh, eps)',
             borrowed=[('T', 'px'), ('P', 'g1'), ('P', 'b1')], ptr='ph1',
             comment='The first layer norm.'),
        dict(args=[26, 4, 5, 18, ONE, LD, LD], impl='linear_implements', hfunc='hLinear',
             x='(h1, wq, bq, l, 1, nh * dh, nh * dh)',
             borrowed=[('T', 'ph1'), ('P', 'wq'), ('P', 'bq')], ptr='pq', comment='The query.'),
        dict(args=[26, 6, 7, 18, ONE, LD, LD], impl='linear_implements', hfunc='hLinear',
             x='(h1, wk, bk, l, 1, nh * dh, nh * dh)',
             borrowed=[('T', 'ph1'), ('P', 'wk'), ('P', 'bk')], ptr='pk', comment='The key.'),
        dict(args=[26, 8, 9, 18, ONE, LD, LD], impl='linear_implements', hfunc='hLinear',
             x='(h1, wv, bv, l, 1, nh * dh, nh * dh)',
             borrowed=[('T', 'ph1'), ('P', 'wv'), ('P', 'bv')], ptr='pv', comment='The value.'),
        dict(args=[27, 28, 1, 18, 19, 20, 21, 23, ('scale', 21)], impl='stepScores_implements',
             hfunc='hScores', x='(q, k, cache, l, p, nh, dh, bsize, 1.0 / dh.toFloat.sqrt)', borrowed=[('T', 'pq'), ('T', 'pk'), ('P', 'cache')], ptr='psc',
             simp_extra=['F64Op.apply', 'F64UnOp.apply', 'F64Bits.toBits_div', 'F64Bits.toBits_sqrt',
                         'F64Convert.toBits_toFloat', 'hOne'],
             comment='The scores against the cached keys and this key.'),
        dict(args=[30, 20, ('add', 19, ONE)], impl='stepSoftmax_implements', hfunc='hSoftmax',
             x='(sc, nh, p + 1)',
             borrowed=[('T', 'psc')], ptr='ppw',
             comment='The softmax of each head.'),
        dict(args=[31, 29, 1, 18, 19, 20, 21, 23], impl='stepMix_implements', hfunc='hMix',
             x='(pw, v, cache, l, p, nh, dh, bsize)',
             borrowed=[('T', 'ppw'), ('T', 'pv'), ('P', 'cache')], ptr='po',
             comment='The weighted sum of the cached values and this value.'),
        dict(args=[32, 10, 11, 18, ONE, LD, LD], impl='linear_implements', hfunc='hLinear',
             x='(o, wo, bo, l, 1, nh * dh, nh * dh)',
             borrowed=[('T', 'po'), ('P', 'wo'), ('P', 'bo')], ptr='pa',
             comment='The attention output.'),
        dict(args=[25, 33], impl='add_implements', hfunc='hAdd', x='(x, a)',
             borrowed=[('T', 'px'), ('T', 'pa')], tail=False, ptr='pr',
             comment='The first residual sum.'),
        dict(args=[34, 12, 13, 18, ONE, LD, ('f', 24)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(r, g2, b2, l, 1, nh * dh, eps)',
             borrowed=[('T', 'pr'), ('P', 'g2'), ('P', 'b2')], ptr='ph2',
             comment='The second layer norm.'),
        dict(args=[35, 14, 15, 16, 17, 18, ONE, LD, 22], impl='mlp_implements', hfunc='hMlp',
             x='(h2, wfc, bfc, wproj, bproj, l, 1, nh * dh, f)',
             borrowed=[('T', 'ph2'), ('P', 'wfc'), ('P', 'bfc'), ('P', 'wproj'), ('P', 'bproj')],
             ptr='pm', comment='The MLP.'),
        dict(args=[34, 36], impl='add_implements', hfunc='hAdd', x='(r, m)',
             borrowed=[('T', 'pr'), ('T', 'pm')], tail=False, ptr='py',
             comment='The second residual sum, the new hidden row.'),
        dict(args=[0, 37, 28, 29, 18, LD], impl='writeBlock_implements', hfunc='hWrite',
             x='(s, y, k, v, l, nh * dh)',
             borrowed=[('P', 's'), ('T', 'py'), ('T', 'pk'), ('T', 'pv')], ptr='pres',
             comment='The block with the new row, key, and value.'),
    ])
LST = tuple_type([k for _, k in LS])
ls_section = tuple_def('layerStepTuple', 'layerStep', LS,
                       '`layerStep` with its twenty-five arguments as one tuple.') + f"""
""" + composite(ls_spec) + '\n'

# ------------------------------------------------------------------ scores
SC = [('cache', 'A'), ('wte', 'A'), ('gf', 'A'), ('bf', 'A'), ('layers', 'u'), ('nh', 'u'), ('dh', 'u'),
      ('vocab', 'u'), ('eps', 'f')]
SD = ('mul', 5, 6)
sc_spec = dict(
    name='scores', entry=42, index=40, tuple='scoresTuple', params=SC, nlocals=4,
    funcs=[('hLast', 39, 37, 'lastHidden'), ('hNorm', 17, 15, 'layerNormRows'),
           ('hScores', 27, 25, 'matMulT')],
    lets=[('x', 'lastHiddenTuple (cache, nh * dh, (2 * layers + 1) * (nh * dh))'),
          ('h', 'layerNormRowsTuple (x, gf, bf, 0, 1, nh * dh, eps)')],
    calls=[
        dict(args=[0, SD, ('mul', ('add', ('mul', ('const', 2), 4), ONE), SD)],
             impl='lastHidden_implements', hfunc='hLast',
             x='(cache, nh * dh, (2 * layers + 1) * (nh * dh))',
             borrowed=[('P', 'cache')], ptr='px', comment='The hidden row of the last block.'),
        dict(args=[9, 2, 3, ('const', 0), ONE, SD, ('f', 8)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(x, gf, bf, 0, 1, nh * dh, eps)',
             borrowed=[('T', 'px'), ('P', 'gf'), ('P', 'bf')], ptr='ph',
             comment='The final layer norm.'),
        dict(args=[10, 1, ONE, SD, 7], impl='matMulT_implements', hfunc='hScores',
             x='(h, wte, 1, nh * dh, vocab)',
             borrowed=[('T', 'ph'), ('P', 'wte')], ptr='pr',
             comment='The scores against every token embedding.'),
    ])
SCT = tuple_type([k for _, k in SC])
sc_section = tuple_def('scoresTuple', 'scores', SC, '`scores` with its nine arguments as one tuple.') + f"""
""" + composite(sc_spec) + '\n'


# ------------------------------------------------------------------ step
STA = ['cache', 'wte', 'wpe'] + BARR[1:]
ST = [(n, 'A') for n in STA] + [('token', 'u'), ('layers', 'u'), ('nh', 'u'), ('dh', 'u'), ('f', 'u'),
                                ('eps', 'f')]
BS = '(2 * layers + 1) * (nh * dh)'
POS = f'UInt64.ofNat cache.size / (if {BS} = 0 then 1 else {BS})'
STEP_F = '(x, cache, ' + ', '.join(BARR[1:]) + f', l, {POS}, nh, dh, f, {BS}, eps)'
st_spec = dict(
    name='step', entry=41, index=39, tuple='stepTuple', params=ST, nlocals=11,
    width=2, result=35,
    funcs=[('hEmbed', 30, 28, 'embedBlock'), ('hLayer', 40, 38, 'layerStep'),
           ('hAppend', 38, 36, 'appendBlock')],
    lets=[('s0', f'embedBlockTuple (wte, wpe, token, {POS}, nh * dh, {BS})'),
          ('xl', f'LeanExe.loop layers s0 fun l x => layerStepTuple {STEP_F}')],
    haves=['  have hA := hCache.values',
           '  have hLength := hA.lengthBound',
           '  simp only [UInt64.toNat_toUInt32] at hLength'],
    calls=[
        dict(kind='run', reg=25, value=BS, reads=[20, 21, 22], comment='The block size.',
             proof='simp [Stmt.run, Expr.eval, {facts}, State.set?_eq_update _ (show 25 < {cur}.params.length + {cur}.locals.length by rw [{curlen}]; decide), U64Op.apply]'),
        dict(kind='run', reg=26, value='UInt64.ofNat cache.size', reads=[0],
             comment='The length of the cache.',
             proof='simp [Stmt.run, Expr.eval, {facts}, hLength, hA.lengthRead, State.set?_eq_update _ (show 26 < {cur}.params.length + {cur}.locals.length by rw [{curlen}]; decide)]'),
        dict(kind='run', reg=27, value=POS, reads=[26, 25], comment='The position.',
             scratch=[(36, 'UInt64.ofNat cache.size'), (37, f'if {BS} = 0 then 1 else {BS}')],
             proof=f'by_cases hb : {BS} = 0 <;> simp [Stmt.run, Expr.eval, {{facts}}, s2, s1, start, State.set?_eq_update, State.update_params_length, State.update_locals_length, State.get_update_ne, U64Op.apply, hb]'),
        dict(args=[1, 2, 19, 27, ('mul', 21, 22), 25], impl='embedBlock_implements',
             hfunc='hEmbed', reg=28, x=f'(wte, wpe, token, {POS}, nh * dh, {BS})', borrowed=[('P', 'wte'), ('P', 'wpe')], ptr='ps0',
             comment='The block of the new position, holding its embedding.'),
        dict(kind='loop', impl='layerStep_implements', hfunc='hLayer', state=29, index=32, src=28,
             init='s0', init_ptr='ps0', count=20,
             args=[29, 0] + list(range(3, 19)) + [32, 27, 21, 22, 23, 25, ('f', 24)], F=STEP_F,
             borrowed=[('P', 'cache')] + [('P', n) for n in BARR[1:]], ptr='pl',
             comment='The layers, each writing its key and value into the block.'),
        dict(args=[0, 29], impl='appendBlock_implements', hfunc='hAppend', reg=34,
             x='(cache, xl)',
             borrowed=[('P', 'cache'), ('T', 'pl')], tail=False, ptr='pr',
             comment='The cache followed by the new block.'),
    ])
STT = tuple_type([k for _, k in ST])
st_pat = ', '.join(n for n, _ in ST)
st_section = f"""/-- The input of `step`: the cache, the embeddings, the stacked weights of the blocks, the
token, and the dimensions. -/
abbrev StepInput := {STT}

/-- `step` with its twenty-five arguments as one tuple. -/
def stepTuple : StepInput → Array Float
  | ({wrap(st_pat, '     ')}) =>
    LeanExe.Examples.Gpt.step {wrap(' '.join(n for n, _ in ST).replace(' ', ', '), '      ', 80).replace(', ', ' ').replace(',', '')}

""" + composite(st_spec) + '\n'


def main():
    text = """import Project.Gpt.StepVerify

/-! Generated by `uv run tools/gpt_composites.py`; do not edit.  The `Implements`
theorems of the GPT functions that call other compiled functions and release their
temporaries, proved with the `Live` invariant. -/

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit

""" + mlp_section + att_section + blk_section + fwd_section + ls_section + sc_section + st_section + "end Project.Gpt\n"
    if sys.argv[1:] == ['--check']:
        if TARGET.read_text() != text:
            raise SystemExit(f'{TARGET} is out of date')
    else:
        TARGET.write_text(text)


main()
