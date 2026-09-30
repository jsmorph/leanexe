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


def arg_ir(a):
    if isinstance(a, tuple):
        if a[0] == 'mul':
            return f'⟨.u64, .bin .mul (.get {a[1]}) (.get {a[2]})⟩'
        if a[0] == 'f':
            return f'⟨.f64, .getF {a[1]}⟩'
        if a[0] == 'scale':
            return (f'⟨.f64, .binF .div (.constF 4607182418800017408) '
                    f'(.unF .sqrt (.convertU (.get {a[1]})))⟩')
    return f'⟨.u64, .get {a}⟩'


def arg_reads(a):
    if isinstance(a, tuple):
        if a[0] == 'mul':
            return [a[1], a[2]]
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


def state_fact(r, depth, nparams):
    """A proof that local `r` of state `s{depth}` holds its value.  State `s{i}` is
    `s{i-1}` (or `start`) with local `nparams + i - 1` updated."""
    def base(i):
        return 'start' if i == 1 else f's{i - 1}'
    if r < nparams:
        term, low = f'sg{r}', 1
    else:
        m = r - nparams + 1
        bound = 'hStart' if m == 1 else f'hS{m - 1}'
        term, low = f'State.get_update_same (state := {base(m)}) (by rw [{bound}]; decide)', m + 1
    for i in range(low, depth + 1):
        term = (f'(State.get_update_ne (state := {base(i)}) (j := {r}) (index := {nparams + i - 1}) '
                f'(by decide)).trans ({term})')
    return term


def eval_lines(args, depth, nparams, ind):
    """The proof that the arguments evaluate, one line per argument."""
    out = []
    for a in args:
        if isinstance(a, tuple) and a[0] == 'mul':
            out.append(f'Expr.evalResults_mul ({state_fact(a[1], depth, nparams)}) '
                       f'({state_fact(a[2], depth, nparams)}) <|')
        elif isinstance(a, tuple) and a[0] == 'f':
            out.append(f'Expr.evalResults_getF ({state_fact(a[1], depth, nparams)}) <|')
        else:
            out.append(f'Expr.evalResults_get ({state_fact(a, depth, nparams)}) <|')
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
    total = nparams + nlocals
    arrays = [n for n, k in params if k in 'AU']
    names = [n for n, _ in params]
    calls = spec['calls']
    L = len(calls)
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
    if spec.get('one'):
        lines.append('  have hOne : (1.0 : Float).toBits = 4607182418800017408 := by decide +kernel')
    for hname, entry, index, ir in spec['funcs']:
        lines.append(f'  have {hname} : gpt.module.funcs[{entry} - gpt.module.imports.length]? =')
        lines.append(f'      some (gpt.{ir}.ir.function (2 + {index})) :=')
        lines.append(f'    compile_funcs (funcs := gpt.funcs) (i := {index}) rfl')
    for n, term in spec['lets']:
        lines.append(f'  let {n} := {term}')
    for h in spec.get('haves', []):
        lines.append(h)
    vals = []
    for n, k in params:
        vals.append(f'.f64 {n}.toBits' if k == 'f' else (f'.i64 {n}' if k == 'u' else f'.i64 {ptr(n)}'))
    lines.append('  let start : State :=')
    lines.append(f'    {{ params := [{wrap(", ".join(vals), "        ")}]')
    lines.append(f'      locals := [{", ".join([".i64 0"] * nlocals)}] }}')
    lines.append(f'  have hStart : start.params.length + start.locals.length = {total} := rfl')
    lines.append('  have hLen : ∀ (s : State) (j : Nat) (v : Value),')
    lines.append('      (s.update j v).params.length + (s.update j v).locals.length =')
    lines.append('        s.params.length + s.locals.length := fun s j v => by')
    lines.append('    simp [State.update_params_length, State.update_locals_length]')
    for j, v in enumerate(vals):
        lines.append(f'  have sg{j} : start.get {j} = some ({v}) := rfl')
    # The body.
    seqs = []
    for n, c in enumerate(calls):
        seqs.append(f"(.call {c['fn']} [{', '.join(arg_ir(a) for a in c['args'])}] [{nparams + n}])")
    seqs.append(f'(.assign {nparams + L} (.get {nparams + L - 1}))')
    temps_regs = list(range(nparams, nparams + L - 1))[::-1]
    for reg in temps_regs[:-1]:
        seqs.append(f'(.release {reg})')
    last = f'(.release {temps_regs[-1]})'
    lines.append('  show Triple _')
    for s in seqs:
        lines.append('    (.seq ' + wrap(s, '      '))
    lines.append(f'    {last}' + ')' * len(seqs) + f' {nparams + nlocals}')
    lines.append('    (fun store state => store = initial ∧ state = start) _')
    # The calls.
    live = '(Live.start hHeap)'
    state = 'start'
    chain = []          # s1, s2, ...
    temps = []          # newest first: pointers
    hprev = 'hStart'
    for n, c in enumerate(calls):
        k = n + 1
        lines.append(f"  -- {c['comment']}")
        lines.append(f"  refine Stmt.seq_spec (Live.call {c['impl']} rfl {c['hfunc']} rfl {live} hRoom")
        lines.append(f"    (x := {c['x']})")
        lines.append(f"    (by simp only [{', '.join(c['need'])}]; omega) (afterArgs := {state})")
        cvals = []
        for a in c['args']:
            if isinstance(a, tuple) and a[0] == 'mul':
                cvals.append(f'.i64 ({spec["mul"][(a[1], a[2])]})')
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
            lines.extend(eval_lines(c['args'], len(chain), nparams, '    '))
        items = []
        for kind, a in c['borrowed']:
            if kind == 'P':
                src = hyp(a) if live == '(Live.start hHeap)' else f'{live}.borrowed {ptr(a)} _ {hyp(a)}'
                items.append((ptr(a), src))
            else:
                items.append((a, f'({live}.tempsOwned _ ({mem(temps.index(a))})).borrowed'))
        lines.append(f"    {wrap(represent(items, c.get('tail', True)), '      ')}")
        lines.append(f'    (by rw [{hprev}]; decide)) ?_')
        lines.append('  apply Triple.of_forall')
        p = c['ptr']
        lines.append(f'  rintro store{k} t{k} ⟨heap{k}, {p}, hLive{k}, rfl⟩')
        lines.append(f'  let s{k} := {state}.update {nparams + n} (.i64 {p})')
        lines.append(f'  have hS{k} : s{k}.params.length + s{k}.locals.length = {total} := by rw [hLen, {hprev}]')
        chain.append(f's{k}')
        state = f's{k}'
        hprev = f'hS{k}'
        live = f'hLive{k}'
        temps.insert(0, p)
        temps_by_reg[nparams + n] = p
    # The result local and the releases.
    res = nparams + L
    sL = f's{L}'
    sR = f's{L + 1}'
    lines.append(f'  let {sR} := {sL}.update {res} (.i64 {calls[-1]["ptr"]})')
    bound_prev = 'hStart' if L == 1 else f'hS{L - 1}'
    sLm = 'start' if L == 1 else f's{L - 1}'
    lines.append(f'  refine Stmt.seq_spec (Stmt.run_spec (final := {sR}) (by')
    lines.append(f'    simp [Stmt.run, Expr.eval, State.set?_eq_update _ (show {res} < {sL}.params.length +')
    lines.append(f'      {sL}.locals.length by rw [hS{L}]; decide), {sR}, {sL}, State.get_update_same,')
    lines.append(f'      show {res - 1} < {sLm}.params.length + {sLm}.locals.length by rw [{bound_prev}]; decide])) ?_')
    lines.append('  -- The temporaries are released, newest first.')
    for n in range(L - 1):
        reg = nparams + n
        lines.append(f'  have r{reg} : {sR}.get {reg} = some (.i64 {calls[n]["ptr"]}) :=')
        lines.append(f'    {state_fact(reg, L + 1, nparams)}')
    live = f'hLive{L}'
    regs = list(range(nparams + L - 2, nparams - 1, -1))
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
    lines.append(f'    by simp [gpt.{name}.ir, Func.scratch, Expr.evalResults, Expr.eval, {sR},')
    lines.append(f'      State.get_update_same, hS{L}], hOwned, hOutB, hOutO⟩')
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
    mul={},
    calls=[
        dict(fn=30, args=[0, 1, 2, 5, 6, 7], impl='linear_implements', hfunc='hLinear',
             x='(x, wfc, bfc, t, d, f)', need=['linearNeed'],
             borrowed=[('P', 'x'), ('P', 'wfc'), ('P', 'bfc')], ptr='ph', comment='`h = x · wfc + bfc`.'),
        dict(fn=13, args=[8], impl='geluArray_implements', hfunc='hGelu', x='h',
             need=['linearNeed', 'geluNeed', 'hSize'], borrowed=[('T', 'ph')], tail=False, ptr='pg',
             comment='`g = gelu h`.'),
        dict(fn=30, args=[9, 3, 4, 5, 7, 6], impl='linear_implements', hfunc='hLinear',
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
    lin_calls.append(dict(fn=30, args=[0, reg, reg + 1, 9, ('mul', 10, 11), ('mul', 10, 11)],
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
          ('o', 'causalMatMulTuple (p, v, t, nh, dh)')],
    mul={(10, 11): 'nh * dh', (9, 10): 't * nh'}, scaleval='.f64 (1.0 / dh.toFloat.sqrt).toBits',
    calls=lin_calls + [
        dict(fn=19, args=[12, 13, 9, 10, 11, ('scale', 11)], impl='maskedScores_implements',
             hfunc='hMasked', x='(q, k, t, nh, dh, 1.0 / dh.toFloat.sqrt)', need=['linearNeed', 'maskedNeed'],
             borrowed=[('T', 'pq'), ('T', 'pk')], ptr='ps',
             simp_extra=['F64Op.apply', 'F64UnOp.apply', 'F64Bits.toBits_div', 'F64Bits.toBits_sqrt',
                         'F64Convert.toBits_toFloat', 'hOne'],
             comment='The masked scores of `q` and `k`, head by head.'),
        dict(fn=23, args=[15, ('mul', 9, 10), 9], impl='softmaxRows_implements', hfunc='hSoftmax',
             x='(s, t * nh, t)', need=['linearNeed', 'maskedNeed', 'softmaxRowsNeed'],
             borrowed=[('T', 'ps')], ptr='pp', comment='The softmax of each of the `t · nh` rows of scores.'),
        dict(fn=26, args=[16, 14, 9, 10, 11], impl='causalMatMul_implements', hfunc='hCausal',
             x='(p, v, t, nh, dh)', need=att_need, borrowed=[('T', 'pp'), ('T', 'pv')], ptr='po',
             comment='`o = p · v`, row `i` summing over rows `0` to `i` of `v`.'),
        dict(fn=30, args=[17, 7, 8, 9, ('mul', 10, 11), ('mul', 10, 11)], impl='linear_implements',
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
    mul={(18, 19): 'nh * dh'},
    calls=[
        dict(fn=18, args=[0, 1, 2, 17, ('mul', 18, 19), ('f', 21)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(x, g1, b1, t, nh * dh, eps)', need=blk_need1,
             borrowed=[('P', 'x'), ('P', 'g1'), ('P', 'b1')], ptr='ph1', comment='The first layer norm.'),
        dict(fn=24, args=[22, 3, 4, 5, 6, 7, 8, 9, 10, 17, 18, 19], impl='attention_implements',
             hfunc='hAttention', x='(h1, wq, bq, wk, bk, wv, bv, wo, bo, t, nh, dh)', need=blk_need2,
             borrowed=[('T', 'ph1')] + [('P', n) for n in ['wq', 'bq', 'wk', 'bk', 'wv', 'bv', 'wo', 'bo']],
             ptr='pa', comment='Attention.'),
        dict(fn=10, args=[0, 23], impl='add_implements', hfunc='hAdd', x='(x, a)', need=blk_need3,
             borrowed=[('P', 'x'), ('T', 'pa')], tail=False, ptr='pr',
             comment='The first residual sum, `r = x + a`.'),
        dict(fn=18, args=[24, 11, 12, 17, ('mul', 18, 19), ('f', 21)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(r, g2, b2, t, nh * dh, eps)', need=blk_need3,
             borrowed=[('T', 'pr'), ('P', 'g2'), ('P', 'b2')], ptr='ph2', comment='The second layer norm.'),
        dict(fn=14, args=[25, 13, 14, 15, 16, 17, ('mul', 18, 19), 20], impl='mlp_implements', hfunc='hMlp',
             x='(h2, wfc, bfc, wproj, bproj, t, nh * dh, f)', need=blk_need5,
             borrowed=[('T', 'ph2'), ('P', 'wfc'), ('P', 'bfc'), ('P', 'wproj'), ('P', 'bproj')], ptr='pm',
             comment='The MLP.'),
        dict(fn=10, args=[24, 26], impl='add_implements', hfunc='hAdd', x='(r, m)', need=blk_need5,
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

# ------------------------------------------------------------------ forward
LA = [n + 'a' for n in BARR[1:]]
LB = [n + 'b' for n in BARR[1:]]
FARR = ['tokens', 'wte', 'wpe'] + LA + LB + ['gf', 'bf']
FWD = [('tokens', 'U')] + [(n, 'A') for n in FARR[1:]] + [('t', 'u'), ('nh', 'u'), ('dh', 'u'), ('f', 'u'),
                                                             ('vocab', 'u'), ('eps', 'f')]
fwd_need = ['embedNeed', 'blockNeed', 'blockBytes', 'attentionBytes', 'hX0']
fwd_spec = dict(
    name='forward', entry=29, index=26, tuple='forwardTuple', need='forwardNeed', params=FWD, nlocals=6,
    room='forwardNeed (' + ', '.join(n for n, _ in FWD) + ')',
    room_unfold=['forwardNeed', 'blockBytes', 'attentionBytes'],
    funcs=[('hEmbed', 27, 24, 'embed'), ('hBlock', 25, 22, 'block'), ('hNorm', 18, 15, 'layerNormRows'),
           ('hScores', 28, 25, 'matMulT')],
    lets=[('x0', 'embedTuple (tokens, wte, wpe, t, nh * dh)'),
          ('x1', 'blockTuple (x0, ' + ', '.join(LA) + ', t, nh, dh, f, eps)'),
          ('x2', 'blockTuple (x1, ' + ', '.join(LB) + ', t, nh, dh, f, eps)'),
          ('h', 'layerNormRowsTuple (x2, gf, bf, t, nh * dh, eps)')],
    haves=['  have hX0 : x0.size = (t * (nh * dh)).toNat := by',
           '    simp [x0, embedTuple, LeanExe.Examples.Gpt.embed, LeanExe.build]',
           '  have hX1 : x1.size ≤ x0.size := block_size_le _'],
    mul={(38, 39): 'nh * dh'},
    calls=[
        dict(fn=27, args=[0, 1, 2, 37, ('mul', 38, 39)], impl='embed_implements', hfunc='hEmbed',
             x='(tokens, wte, wpe, t, nh * dh)', need=['embedNeed'],
             borrowed=[('P', 'tokens'), ('P', 'wte'), ('P', 'wpe')], ptr='px0', comment='The embeddings.'),
        dict(fn=25, args=[43] + list(range(3, 19)) + [37, 38, 39, 40, ('f', 42)], impl='block_implements',
             hfunc='hBlock', x='(x0, ' + ', '.join(LA) + ', t, nh, dh, f, eps)', need=fwd_need,
             borrowed=[('T', 'px0')] + [('P', n) for n in LA], ptr='px1', comment='The first block.'),
        dict(fn=25, args=[44] + list(range(19, 35)) + [37, 38, 39, 40, ('f', 42)], impl='block_implements',
             hfunc='hBlock', x='(x1, ' + ', '.join(LB) + ', t, nh, dh, f, eps)', need=fwd_need,
             borrowed=[('T', 'px1')] + [('P', n) for n in LB], ptr='px2', comment='The second block.'),
        dict(fn=18, args=[45, 35, 36, 37, ('mul', 38, 39), ('f', 42)], impl='layerNormRows_implements',
             hfunc='hNorm', x='(x2, gf, bf, t, nh * dh, eps)', need=fwd_need + ['layerNormRowsNeed'],
             borrowed=[('T', 'px2'), ('P', 'gf'), ('P', 'bf')], ptr='ph', comment='The final layer norm.'),
        dict(fn=28, args=[46, 1, 37, ('mul', 38, 39), 41], impl='matMulT_implements', hfunc='hScores',
             x='(h, wte, t, nh * dh, vocab)', need=fwd_need + ['layerNormRowsNeed', 'matMulTNeed'],
             borrowed=[('T', 'ph'), ('P', 'wte')], ptr='pr',
             comment='The scores against every token embedding.'),
    ],
    finish=fwd_need[:-1] + ['layerNormRowsNeed', 'matMulTNeed', 'forwardNeed', 'hX0'])
FT = tuple_type([k for _, k in FWD])
pat = ', '.join(n for n, _ in FWD)
fwd_section = f'''/-- A block's result is no longer than its input. -/
theorem block_size_le (x : {BT}) : (blockTuple x).size ≤ x.1.size := by
  simp [blockTuple, LeanExe.Examples.Gpt.block, LeanExe.Examples.Gpt.add, LeanExe.build,
    Nat.mod_le]

/-- The input of `forward`: the tokens, the embeddings, the weights of two blocks, the final
layer norm, and the dimensions. -/
abbrev ForwardInput := {FT}

/-- `forward` with its forty-three arguments as one tuple. -/
def forwardTuple : ForwardInput → Array Float
  | ({wrap(pat, '     ')}) =>
    LeanExe.Examples.Gpt.forward {wrap(' '.join(n for n, _ in FWD).replace(' ', ', '), '      ', 80).replace(', ', ' ').replace(',', '')}

/-- The bytes `forward` may allocate: the embeddings, two blocks, the final layer norm,
and the scores. -/
def forwardNeed : ForwardInput → Nat
  | ({wrap(', '.join(['_'] * 37), '     ')}, t, nh, dh, f, vocab, _) =>
    48 + 8 * ((t * (nh * dh)).toNat + 1) + blockBytes t nh dh f (t * (nh * dh)).toNat +
      blockBytes t nh dh f (t * (nh * dh)).toNat +
      (48 + 8 * (t.toNat + 1) + (48 + 8 * (t.toNat + 1)) + (48 + 8 * ((t * (nh * dh)).toNat + 1))) +
      (48 + 8 * ((t * vocab).toNat + 1))

''' + composite(fwd_spec) + '\n'



def main():
    text = """import Project.Gpt.Verify

/-! Generated by `uv run tools/gpt_composites.py`; do not edit.  The `Implements`
theorems of the GPT functions that call other compiled functions and release their
temporaries, proved with the `Live` invariant. -/

namespace Project.Gpt

open Wasm Project.Pipeline Project.IR Project.Runtime Project.ProofKit

""" + mlp_section + att_section + blk_section + fwd_section + "end Project.Gpt\n"
    if sys.argv[1:] == ['--check']:
        if TARGET.read_text() != text:
            raise SystemExit(f'{TARGET} is out of date')
    else:
        TARGET.write_text(text)


main()
