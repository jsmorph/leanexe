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
        if a[0] == 'mul':
            return arg_reads(a[1]) + arg_reads(a[2])
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
    """A proof that the `u64` expression `e`, a local or a product, evaluates; `fact(r)`
    proves that local `r` holds its value."""
    if isinstance(e, tuple):
        return f'Expr.eval_mul ({eval_term(e[1], fact)}) ({eval_term(e[2], fact)})'
    return f'Expr.eval_get ({fact(e)})'


def value_term(e, names):
    """The value of the `u64` expression `e` in terms of the parameter names."""
    if isinstance(e, tuple):
        right = value_term(e[2], names)
        if isinstance(e[2], tuple):
            right = f'({right})'
        return f'{value_term(e[1], names)} * {right}'
    return names[e]


def eval_lines(args, fact, ind):
    """The proof that the arguments evaluate, one line per argument."""
    out = []
    for a in args:
        if isinstance(a, tuple) and a[0] == 'mul':
            out.append(f'Expr.evalResults_u64 ({eval_term(a, fact)}) <|')
        elif isinstance(a, tuple) and a[0] == 'f':
            out.append(f'Expr.evalResults_getF ({fact(a[1])}) <|')
        else:
            out.append(f'Expr.evalResults_get ({fact(a)}) <|')
    out.append('Expr.evalResults_nil')
    out[0] = '(' + out[0]
    out[-1] = out[-1] + ')'
    return [ind + out[0]] + [ind + '  ' + line for line in out[1:]]


def composite(spec):
    temps_by_reg = {}
    name = spec['name']
    params = spec['params']            # list of (name, kind): 'A', 'U', 'u', 'f'
    nparams = len(params)
    nlocals = spec['nlocals']
    width = spec.get('width', 0)
    total = nparams + nlocals + width
    arrays = [n for n, k in params if k in 'AU']
    names = [n for n, _ in params]
    calls = spec['calls']
    L = len(calls)
    loops = any(c.get('kind') == 'loop' for c in calls)
    lines = []
    if spec.get('heartbeats'):
        lines.append('set_option maxHeartbeats 1000000 in')
    lines.append(f"theorem {name}_implements : Implements gpt.module {spec['entry']} "
                 f"{spec['tuple']} {spec['need']} := by")
    lines.append(f"  refine Func.implements_heap gpt.funcs {spec['index']} gpt.{name}.ir \"{name}\" rfl")
    lines.append(f"    {spec['tuple']} {spec['need']}")
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
    lines.append(f'  rintro ⟨{wrap(", ".join(names), "    ")}⟩ heap initial _ hHeap hArgs hRoom')
    for n, k in params:
        if k in 'AU':
            lines.append(f'  obtain ⟨{ptr(n)}, _, rfl, {hyp(n)}, hArgs⟩ := {lemma[k]} hArgs')
    lines.append('  obtain rfl := hArgs')
    lines.append(f"  change heap.Room initial gpt.module ({spec['room']}) at hRoom")
    if spec.get('room_unfold'):
        lines.append(f"  simp only [{', '.join(spec['room_unfold'])}] at hRoom")
    lines.append('  have hImports : gpt.module.imports = [] := rfl')
    lines.append('  have hRelease : gpt.module.funcs[2]? = some (releaseFunction 1) := rfl')
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
    for n, c in enumerate(calls):
        k = n + 1
        cur = states[-1]
        lines.append(f"  -- {c['comment']}")
        if c.get('kind') == 'loop':
            p = c['ptr']
            lines.append(f"  refine Live.arrayLoop {c['impl']} rfl {c['hfunc']} rfl hMemory32 hImports hAlloc")
            lines.append(f"    hRelease (by decide) (by decide) (by decide) (by decide) (by rw [{cur['len']}]; decide)")
            lines.append(f"    {live} hRoom ({fact(c['src'])})")
            lines.append(f"    ({live}.tempsOwned _ ({mem(temps.index(c['init_ptr']))})).borrowed (init := {c['init']})")
            lines.append(f"    (fun _ st hF => ⟨_, Expr.eval_get ((hF.get {c['count']} (by decide) (by decide)).trans")
            lines.append(f"      ({fact(c['count'])}))⟩)")
            lines.append(f"    (fun l x => {wrap(c['F'], '      ')})")
            lines.append(f"    (bound := {c['bound']}) (fun k _ => {c['bound_proof']})")
            lines.append(f"    (by simp only [{', '.join(c['need'])}]; omega)")
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
                    cvals.append(f'.i64 ({value_term(a, names)})')
                else:
                    cvals.append(vals[a])
            lines.append(f"    (fun k p _ _ _ st _ hF hI hSt hL =>")
            lines.append(f"      ⟨[{wrap(', '.join(cvals), '        ')}], st,")
            body = eval_lines(c['args'], inner, '        ')
            body[-1] += ','
            lines.extend(body)
            items = [('p', '(hL.tempsOwned _ (List.mem_cons_self ..)).borrowed')]
            items += [(ptr(a), f'hL.borrowed {ptr(a)} _ {hyp(a)}') for kind, a in c['borrowed']]
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
        lines.append(f"  refine Live.call_seq {c['impl']} rfl {c['hfunc']} rfl {live} hRoom")
        lines.append(f"    (x := {c['x']})")
        lines.append(f"    (by simp only [{', '.join(c['need'])}]; omega) (afterArgs := {cur['name']})")
        cvals = []
        for a in c['args']:
            if isinstance(a, tuple) and a[0] == 'mul':
                cvals.append(f'.i64 ({value_term(a, names)})')
            elif isinstance(a, tuple) and a[0] == 'f':
                cvals.append(vals[a[1]])
            elif isinstance(a, tuple) and a[0] == 'scale':
                cvals.append(spec['scaleval'])
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
                src = hyp(a) if live == '(Live.start hHeap)' else f'{live}.borrowed {ptr(a)} _ {hyp(a)}'
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
    items = [(ptr(n), f'hKeep {ptr(n)} _ {hyp(n)}') for n in arrays]
    tup = '(' + ', '.join(names) + ')'
    lines.append("  have hParams : ∀ (heap' : Heap) (store' : Store Unit),")
    lines.append("      (∀ p ws, heap.Borrowed initial p ws → heap'.Borrowed store' p ws) →")
    lines.append(f"      Represent.borrowed heap' store' [{wrap(', '.join(vals), '        ')}]")
    lines.append(f"        {wrap(tup, '        ')} := fun heap' store' hKeep =>")
    lines.append(f"    {wrap(represent(items, True), '      ')}")
    lines.append("  obtain ⟨heap', hAt', hArgs', hTop', hPages', hCaps', hKeepB, hKeepO, hOwned, hOutB, hOutO⟩ :=")
    lines.append(f"    {live}.finish (need := {spec['need']} {wrap(tup, '      ')})")
    lines.append(f"      (by simp only [{wrap(', '.join(spec['finish']), '          ')}]")
    lines.append('          omega) hParams')
    lines.append(f"  exact ⟨heap', hAt', hArgs', hTop', hPages', hCaps', hKeepB, hKeepO, [.i64 {calls[-1]['ptr']}], {sR},")
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
MLP = [('x', 'A'), ('wfc', 'A'), ('bfc', 'A'), ('wproj', 'A'), ('bproj', 'A'), ('t', 'u'), ('d', 'u'),
       ('f', 'u')]
mlp_spec = dict(
    name='mlp', entry=14, index=11, tuple='mlpTuple', need='mlpNeed', params=MLP, nlocals=4,
    room='mlpNeed (x, wfc, bfc, wproj, bproj, t, d, f)', room_unfold=['mlpNeed'],
    funcs=[('hLinear', 30, 27, 'linear'), ('hGelu', 13, 10, 'geluArray')],
    lets=[('h', 'linearTuple (x, wfc, bfc, t, d, f)'), ('g', 'LeanExe.Examples.Gpt.geluArray h')],
    haves=['  have hSize : h.size = (t * f).toNat := linear_size x wfc bfc t d f'],
    calls=[
        dict(args=[0, 1, 2, 5, 6, 7], impl='linear_implements', hfunc='hLinear',
             x='(x, wfc, bfc, t, d, f)', need=['linearNeed'],
             borrowed=[('P', 'x'), ('P', 'wfc'), ('P', 'bfc')], ptr='ph', comment='`h = x · wfc + bfc`.'),
        dict(args=[8], impl='geluArray_implements', hfunc='hGelu', x='h',
             need=['linearNeed', 'geluNeed', 'hSize'], borrowed=[('T', 'ph')], tail=False, ptr='pg',
             comment='`g = gelu h`.'),
        dict(args=[9, 3, 4, 5, 7, 6], impl='linear_implements', hfunc='hLinear',
             x='(g, wproj, bproj, t, f, d)', need=['linearNeed', 'geluNeed', 'hSize'],
             borrowed=[('T', 'pg'), ('P', 'wproj'), ('P', 'bproj')], ptr='pr',
             comment='The result, `g · wproj + bproj`.'),
    ],
    finish=['linearNeed', 'geluNeed', 'mlpNeed', 'hSize'])
mlp_section = tuple_def('mlpTuple', 'mlp', MLP, '`mlp` with its eight arguments as one tuple.') + f'''
/-- The bytes `mlp` may allocate: two `t × f` arrays and the `t × d` result. -/
def mlpNeed (x : {tuple_type([k for _, k in MLP])}) : Nat :=
  48 + 8 * (({proj(8, 5)} * {proj(8, 7)}).toNat + 1) +
    (48 + 8 * (({proj(8, 5)} * {proj(8, 7)}).toNat + 1)) +
    (48 + 8 * (({proj(8, 5)} * {proj(8, 6)}).toNat + 1))

''' + composite(mlp_spec) + '\n'

# ------------------------------------------------------------------ attention
ATT = [(n, 'A') for n in ['x', 'wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo']] + [('t', 'u'), ('nh', 'u'), ('dh', 'u')]
lin_calls = []
for idx, (w, b, ptrname, reg) in enumerate([('wq', 'bq', 'pq', 1), ('wk', 'bk', 'pk', 3), ('wv', 'bv', 'pv', 5)]):
    lin_calls.append(dict(args=[0, reg, reg + 1, 9, ('mul', 10, 11), ('mul', 10, 11)],
                          impl='linear_implements', hfunc='hLinear', x=f'(x, {w}, {b}, t, nh * dh, nh * dh)',
                          need=['linearNeed'], borrowed=[('P', 'x'), ('P', w), ('P', b)], ptr=ptrname,
                          comment=f'`{ptrname[1]} = x · {w} + {b}`.'))
att_need = ['linearNeed', 'maskedNeed', 'softmaxRowsNeed', 'causalMatMulNeed']
att_spec = dict(
    name='attention', entry=24, index=21, tuple='attentionTuple', need='attentionNeed', params=ATT,
    nlocals=8, one=True, room='attentionBytes t nh dh', room_unfold=['attentionBytes'],
    funcs=[('hLinear', 30, 27, 'linear'), ('hMasked', 19, 16, 'maskedScores'),
           ('hSoftmax', 23, 20, 'softmaxRows'), ('hCausal', 26, 23, 'causalMatMul')],
    lets=[('q', 'linearTuple (x, wq, bq, t, nh * dh, nh * dh)'),
          ('k', 'linearTuple (x, wk, bk, t, nh * dh, nh * dh)'),
          ('v', 'linearTuple (x, wv, bv, t, nh * dh, nh * dh)'),
          ('s', 'maskedTuple (q, k, t, nh, dh, 1.0 / dh.toFloat.sqrt)'),
          ('p', 'softmaxRowsTuple (s, t * nh, t)'),
          ('o', 'causalMatMulTuple (p, v, t, nh, dh)')], scaleval='.f64 (1.0 / dh.toFloat.sqrt).toBits',
    calls=lin_calls + [
        dict(args=[12, 13, 9, 10, 11, ('scale', 11)], impl='maskedScores_implements',
             hfunc='hMasked', x='(q, k, t, nh, dh, 1.0 / dh.toFloat.sqrt)', need=['linearNeed', 'maskedNeed'],
             borrowed=[('T', 'pq'), ('T', 'pk')], ptr='ps',
             simp_extra=['F64Op.apply', 'F64UnOp.apply', 'F64Bits.toBits_div', 'F64Bits.toBits_sqrt',
                         'F64Convert.toBits_toFloat', 'hOne'],
             comment='The masked scores of `q` and `k`, head by head.'),
        dict(args=[15, ('mul', 9, 10), 9], impl='softmaxRows_implements', hfunc='hSoftmax',
             x='(s, t * nh, t)', need=['linearNeed', 'maskedNeed', 'softmaxRowsNeed'],
             borrowed=[('T', 'ps')], ptr='pp', comment='The softmax of each of the `t · nh` rows of scores.'),
        dict(args=[16, 14, 9, 10, 11], impl='causalMatMul_implements', hfunc='hCausal',
             x='(p, v, t, nh, dh)', need=att_need, borrowed=[('T', 'pp'), ('T', 'pv')], ptr='po',
             comment='`o = p · v`, row `i` summing over rows `0` to `i` of `v`.'),
        dict(args=[17, 7, 8, 9, ('mul', 10, 11), ('mul', 10, 11)], impl='linear_implements',
             hfunc='hLinear', x='(o, wo, bo, t, nh * dh, nh * dh)', need=att_need,
             borrowed=[('T', 'po'), ('P', 'wo'), ('P', 'bo')], ptr='pr', comment='The result, `o · wo + bo`.'),
    ],
    finish=att_need + ['attentionNeed', 'attentionBytes'])
att_section = tuple_def('attentionTuple', 'attention', ATT, '`attention` with its twelve arguments as one tuple.') + '''
/-- The bytes `attention` may allocate for `t` rows and `nh` heads of width `dh`: `q`, `k`,
and `v`, the scores, the softmax with its two temporaries, the weighted values, and the
result. -/
def attentionBytes (t nh dh : UInt64) : Nat :=
  48 + 8 * ((t * (nh * dh)).toNat + 1) + (48 + 8 * ((t * (nh * dh)).toNat + 1)) +
    (48 + 8 * ((t * (nh * dh)).toNat + 1)) + (48 + 8 * ((t * nh * t).toNat + 1)) +
    (48 + 8 * ((t * nh).toNat + 1) + (48 + 8 * ((t * nh).toNat + 1)) +
      (48 + 8 * ((t * nh * t).toNat + 1))) +
    (48 + 8 * ((t * (nh * dh)).toNat + 1)) + (48 + 8 * ((t * (nh * dh)).toNat + 1))

/-- The bytes `attention` may allocate. -/
def attentionNeed (x : ''' + tuple_type([k for _, k in ATT]) + f''') : Nat :=
  attentionBytes {proj(12, 9)} {proj(12, 10)} {proj(12, 11)}

''' + composite(att_spec) + '\n'

# ------------------------------------------------------------------ block
BARR = ['x', 'g1', 'b1', 'wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo', 'g2', 'b2', 'wfc', 'bfc', 'wproj', 'bproj']
BLK = [(n, 'A') for n in BARR] + [('t', 'u'), ('nh', 'u'), ('dh', 'u'), ('f', 'u'), ('eps', 'f')]
blk_need1 = ['layerNormRowsNeed']
blk_need2 = blk_need1 + ['attentionNeed', 'attentionBytes']
blk_need3 = blk_need2 + ['addNeed']
blk_need5 = blk_need3 + ['mlpNeed']
blk_spec = dict(
    name='block', entry=25, index=22, tuple='blockTuple', need='blockNeed', params=BLK, nlocals=7,
    room='blockBytes t nh dh f x.size', room_unfold=['blockBytes', 'attentionBytes'],
    funcs=[('hNorm', 18, 15, 'layerNormRows'), ('hAttention', 24, 21, 'attention'), ('hAdd', 10, 7, 'add'),
           ('hMlp', 14, 11, 'mlp')],
    lets=[('h1', 'layerNormRowsTuple (x, g1, b1, t, nh * dh, eps)'),
          ('a', 'attentionTuple (h1, wq, bq, wk, bk, wv, bv, wo, bo, t, nh, dh)'),
          ('r', 'addTuple (x, a)'),
          ('h2', 'layerNormRowsTuple (r, g2, b2, t, nh * dh, eps)'),
          ('m', 'mlpTuple (h2, wfc, bfc, wproj, bproj, t, nh * dh, f)')],
    haves=['  have hR : r.size ≤ x.size := add_size_le x a'],
    calls=[
        dict(args=[0, 1, 2, 17, ('mul', 18, 19), ('f', 21)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(x, g1, b1, t, nh * dh, eps)', need=blk_need1,
             borrowed=[('P', 'x'), ('P', 'g1'), ('P', 'b1')], ptr='ph1', comment='The first layer norm.'),
        dict(args=[22, 3, 4, 5, 6, 7, 8, 9, 10, 17, 18, 19], impl='attention_implements',
             hfunc='hAttention', x='(h1, wq, bq, wk, bk, wv, bv, wo, bo, t, nh, dh)', need=blk_need2,
             borrowed=[('T', 'ph1')] + [('P', n) for n in ['wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo']],
             ptr='pa', comment='Attention.'),
        dict(args=[0, 23], impl='add_implements', hfunc='hAdd', x='(x, a)', need=blk_need3,
             borrowed=[('P', 'x'), ('T', 'pa')], tail=False, ptr='pr',
             comment='The first residual sum, `r = x + a`.'),
        dict(args=[24, 11, 12, 17, ('mul', 18, 19), ('f', 21)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(r, g2, b2, t, nh * dh, eps)', need=blk_need3,
             borrowed=[('T', 'pr'), ('P', 'g2'), ('P', 'b2')], ptr='ph2', comment='The second layer norm.'),
        dict(args=[25, 13, 14, 15, 16, 17, ('mul', 18, 19), 20], impl='mlp_implements', hfunc='hMlp',
             x='(h2, wfc, bfc, wproj, bproj, t, nh * dh, f)', need=blk_need5,
             borrowed=[('T', 'ph2'), ('P', 'wfc'), ('P', 'bfc'), ('P', 'wproj'), ('P', 'bproj')], ptr='pm',
             comment='The MLP.'),
        dict(args=[24, 26], impl='add_implements', hfunc='hAdd', x='(r, m)', need=blk_need5,
             borrowed=[('T', 'pr'), ('T', 'pm')], tail=False, ptr='pres', comment='The result, `r + m`.'),
    ],
    finish=blk_need5 + ['blockNeed', 'blockBytes'])
BT = tuple_type([k for _, k in BLK])
blk_section = tuple_def('blockTuple', 'block', BLK, '`block` with its twenty-two arguments as one tuple.') + f'''
/-- The bytes `block` may allocate for `t` rows, `nh` heads of width `dh`, hidden width `f`,
and an input of `n` elements: two layer norms, attention, two sums, and the MLP. -/
def blockBytes (t nh dh f : UInt64) (n : Nat) : Nat :=
  48 + 8 * (t.toNat + 1) + (48 + 8 * (t.toNat + 1)) + (48 + 8 * ((t * (nh * dh)).toNat + 1)) +
    attentionBytes t nh dh + (48 + 8 * (n + 1)) +
    (48 + 8 * (t.toNat + 1) + (48 + 8 * (t.toNat + 1)) + (48 + 8 * ((t * (nh * dh)).toNat + 1))) +
    (48 + 8 * ((t * f).toNat + 1) + (48 + 8 * ((t * f).toNat + 1)) +
      (48 + 8 * ((t * (nh * dh)).toNat + 1))) +
    (48 + 8 * (n + 1))

/-- The bytes `block` may allocate. -/
def blockNeed (x : {BT}) : Nat :=
  blockBytes {proj(22, 17)} {proj(22, 18)}
    {proj(22, 19)} {proj(22, 20)} x.1.size

''' + composite(blk_spec) + '\n'

# ------------------------------------------------------------------ blockAt
BAT = [(n, 'A') for n in BARR] + [('l', 'u'), ('t', 'u'), ('nh', 'u'), ('dh', 'u'), ('f', 'u'),
                                   ('eps', 'f')]
BAT_NAMES = [n for n, _ in BAT]
D = ('mul', 19, 20)
DD = ('mul', D, D)
DF = ('mul', D, 21)
FD = ('mul', 21, D)
SLICES = [('g1', 1, D), ('b1', 2, D), ('wq', 3, DD), ('bq', 4, D), ('wk', 5, DD), ('bk', 6, D),
          ('wv', 7, DD), ('bv', 8, D), ('wo', 9, DD), ('bo', 10, D), ('g2', 11, D), ('b2', 12, D),
          ('wfc', 13, DF), ('bfc', 14, 21), ('wproj', 15, FD), ('bproj', 16, D)]
bat_calls = []
bat_lets = []
for nm, reg, size in SLICES:
    start = ('mul', 17, size)
    x = f'({nm}, {value_term(start, BAT_NAMES)}, {value_term(size, BAT_NAMES)})'
    bat_lets.append((nm + 'l', f'sliceTuple {x}'))
    bat_calls.append(dict(args=[reg, start, size], impl='slice_implements', hfunc='hSlice', x=x,
                          need=['sliceNeed'], borrowed=[('P', nm)], ptr='l' + cap(nm),
                          comment=f'Layer `l` of `{nm}`.'))
bat_need = ['sliceNeed', 'blockNeed', 'blockBytes', 'attentionBytes']
bat_calls.append(dict(args=[0] + list(range(23, 39)) + [18, 19, 20, 21, ('f', 22)],
                      impl='block_implements', hfunc='hBlock',
                      x='(x, ' + ', '.join(nm + 'l' for nm, _, _ in SLICES) + ', t, nh, dh, f, eps)',
                      need=bat_need,
                      borrowed=[('P', 'x')] + [('T', 'l' + cap(nm)) for nm, _, _ in SLICES],
                      ptr='pr', comment="The block with layer `l`'s weights."))
bat_spec = dict(
    name='blockAt', entry=32, index=29, tuple='blockAtTuple', need='blockAtNeed', params=BAT, nlocals=18,
    room='blockAtNeed (' + ', '.join(BAT_NAMES) + ')',
    room_unfold=['blockAtNeed', 'blockAtBytes', 'blockBytes', 'attentionBytes'],
    funcs=[('hSlice', 31, 28, 'slice'), ('hBlock', 25, 22, 'block')],
    lets=bat_lets, calls=bat_calls,
    finish=bat_need + ['blockAtNeed', 'blockAtBytes'])
BATT = tuple_type([k for _, k in BAT])
bat_section = tuple_def('blockAtTuple', 'blockAt', BAT,
                        '`blockAt` with its twenty-three arguments as one tuple.') + f"""
/-- The bytes `blockAt` may allocate for an input of `n` elements: the sixteen slices of
layer `l`'s weights and the block. -/
def blockAtBytes (t nh dh f : UInt64) (n : Nat) : Nat :=
  9 * (48 + 8 * ((nh * dh).toNat + 1)) + 4 * (48 + 8 * ((nh * dh * (nh * dh)).toNat + 1)) +
    (48 + 8 * ((nh * dh * f).toNat + 1)) + (48 + 8 * (f.toNat + 1)) +
    (48 + 8 * ((f * (nh * dh)).toNat + 1)) + blockBytes t nh dh f n

/-- The bytes `blockAt` may allocate. -/
def blockAtNeed (x : {BATT}) : Nat :=
  blockAtBytes {proj(23, 18)} {proj(23, 19)}
    {proj(23, 20)} {proj(23, 21)} x.1.size

""" + composite(bat_spec) + '\n'


# ------------------------------------------------------------------ forward
LAYER = BARR[1:]
FWD = ([('tokens', 'U'), ('wte', 'A'), ('wpe', 'A')] + [(n, 'A') for n in LAYER] +
       [('gf', 'A'), ('bf', 'A'), ('layers', 'u'), ('t', 'u'), ('nh', 'u'), ('dh', 'u'), ('f', 'u'),
        ('vocab', 'u'), ('eps', 'f')])
FWD_NAMES = [n for n, _ in FWD]
LAYER_F = '(x, ' + ', '.join(LAYER) + ', l, t, nh, dh, f, eps)'
fwd_need = ['embedNeed', 'hX0']
fwd_spec = dict(
    name='forward', entry=29, index=26, tuple='forwardTuple', need='forwardNeed', params=FWD,
    nlocals=9, width=1, result=36,
    room='forwardNeed (' + ', '.join(FWD_NAMES) + ')', room_unfold=['forwardNeed'],
    funcs=[('hEmbed', 27, 24, 'embed'), ('hBlockAt', 32, 29, 'blockAt'),
           ('hNorm', 18, 15, 'layerNormRows'), ('hScores', 28, 25, 'matMulT')],
    lets=[('x0', 'embedTuple (tokens, wte, wpe, t, nh * dh)'),
          ('xl', f'LeanExe.loop layers x0 fun l x => blockAtTuple {LAYER_F}'),
          ('h', 'layerNormRowsTuple (xl, gf, bf, t, nh * dh, eps)')],
    haves=['  have hX0 : x0.size = (t * (nh * dh)).toNat := by',
           '    simp [x0, embedTuple, LeanExe.Examples.Gpt.embed, LeanExe.build]',
           '  have hSizes : ∀ k,',
           f'      (loopPrefix (fun l x => blockAtTuple {wrap(LAYER_F, "        ")}) x0 k).size ≤',
           '      (t * (nh * dh)).toNat := fun k =>',
           f'    Nat.le_trans (loopPrefix_size_le (fun l x => blockAt_size_le {wrap(LAYER_F, "      ")}) k)',
           '      hX0.le'],
    calls=[
        dict(args=[0, 1, 2, 22, ('mul', 23, 24)], impl='embed_implements', hfunc='hEmbed', reg=28,
             x='(tokens, wte, wpe, t, nh * dh)', need=['embedNeed'],
             borrowed=[('P', 'tokens'), ('P', 'wte'), ('P', 'wpe')], ptr='px0', comment='The embeddings.'),
        dict(kind='loop', impl='blockAt_implements', hfunc='hBlockAt', state=29, index=32, src=28,
             init='x0', init_ptr='px0', count=21,
             args=[29] + list(range(3, 19)) + [32, 22, 23, 24, 25, ('f', 27)], F=LAYER_F,
             bound='blockAtBytes t nh dh f (t * (nh * dh)).toNat',
             bound_proof='blockAtBytes_le (hSizes k)', need=fwd_need,
             borrowed=[('P', n) for n in LAYER], ptr='pl', comment='The blocks, one per layer.'),
        dict(args=[29, 19, 20, 22, ('mul', 23, 24), ('f', 27)], impl='layerNormRows_implements',
             hfunc='hNorm', reg=34, x='(xl, gf, bf, t, nh * dh, eps)',
             need=fwd_need + ['layerNormRowsNeed'], borrowed=[('T', 'pl'), ('P', 'gf'), ('P', 'bf')],
             ptr='ph', comment='The final layer norm.'),
        dict(args=[34, 1, 22, ('mul', 23, 24), 26], impl='matMulT_implements', hfunc='hScores', reg=35,
             x='(h, wte, t, nh * dh, vocab)', need=fwd_need + ['layerNormRowsNeed', 'matMulTNeed'],
             borrowed=[('T', 'ph'), ('P', 'wte')], ptr='pr',
             comment='The scores against every token embedding.'),
    ],
    finish=['embedNeed', 'layerNormRowsNeed', 'matMulTNeed', 'forwardNeed', 'hX0'])
FT = tuple_type([k for _, k in FWD])
pat = ', '.join(FWD_NAMES)
fwd_section = f"""/-- A block's result is no longer than its input. -/
theorem block_size_le (x : {BT}) : (blockTuple x).size ≤ x.1.size := by
  simp [blockTuple, LeanExe.Examples.Gpt.block, LeanExe.Examples.Gpt.add, LeanExe.build,
    Nat.mod_le]

/-- `blockAt`'s result is no longer than its input. -/
theorem blockAt_size_le (x : {BATT}) : (blockAtTuple x).size ≤ x.1.size := by
  simp [blockAtTuple, LeanExe.Examples.Gpt.blockAt, LeanExe.Examples.Gpt.block,
    LeanExe.Examples.Gpt.add, LeanExe.build, Nat.mod_le]

theorem blockAtBytes_le {{t nh dh f : UInt64}} {{n n' : Nat}} (h : n ≤ n') :
    blockAtBytes t nh dh f n ≤ blockAtBytes t nh dh f n' := by
  simp only [blockAtBytes, blockBytes]
  omega

/-- The input of `forward`: the tokens, the embeddings, the stacked weights of the blocks,
the final layer norm, and the dimensions. -/
abbrev ForwardInput := {FT}

/-- `forward` with its twenty-eight arguments as one tuple. -/
def forwardTuple : ForwardInput → Array Float
  | ({wrap(pat, '     ')}) =>
    LeanExe.Examples.Gpt.forward {wrap(' '.join(FWD_NAMES).replace(' ', ', '), '      ', 80).replace(', ', ' ').replace(',', '')}

/-- The bytes `forward` may allocate: the embeddings, their copy, `layers` calls of
`blockAt`, the final layer norm, and the scores. -/
def forwardNeed : ForwardInput → Nat
  | ({wrap(', '.join(['_'] * 21), '     ')}, layers, t, nh, dh, f, vocab, _) =>
    48 + 8 * ((t * (nh * dh)).toNat + 1) + (48 + 8 * ((t * (nh * dh)).toNat + 1)) +
      layers.toNat * blockAtBytes t nh dh f (t * (nh * dh)).toNat +
      (48 + 8 * (t.toNat + 1) + (48 + 8 * (t.toNat + 1)) + (48 + 8 * ((t * (nh * dh)).toNat + 1))) +
      (48 + 8 * ((t * vocab).toNat + 1))

""" + composite(fwd_spec) + '\n'


def main():
    text = """import Project.Gpt.Verify

/-! Generated by `uv run tools/gpt_composites.py`; do not edit.  The `Implements`
theorems of the GPT functions that call other compiled functions and release their
temporaries, proved with the `Live` invariant. -/

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit

""" + mlp_section + att_section + blk_section + bat_section + fwd_section + "end Project.Gpt\n"
    if sys.argv[1:] == ['--check']:
        if TARGET.read_text() != text:
            raise SystemExit(f'{TARGET} is out of date')
    else:
        TARGET.write_text(text)


main()
