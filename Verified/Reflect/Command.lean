import Verified.Correct
import Verified.Reflect.Lemmas
import Verified.Reflect.Modes
import LeanExe.Encoding.RoundTrip

/-! The reflector.  `verified_compile p := [f, g, …]` reads the listed Lean definitions, writes
each as a source function, and proves its equation `denote (reflect f) = f` from the lemmas of
`Verified.Reflect.Lemmas`, composed term by term.  It adds the program `p.program`, the module
`p.module := compile p.prog`, in which the `k`-th definition is function `2 + k`, and for each
definition `f` the source function `p.f.func`, the equation `p.f.denote_eq`, and the theorem
`p.f.implements` that the module computes `f`.  `p.bytes` states that the module's bytes decode
to a module that computes every listed definition.

The reflector is meta code and is not trusted: Lean's kernel checks every equation it builds, and
the theorem holds for the parameter modes that `Expr.paramChoice` chooses as for any others.  A
definition's parameters and result are `UInt64`, `Bool`, `Array UInt64`, or pairs of them.  Its
body may use literals and other closed terms, its parameters, `let`, the word operations `+`, `-`,
`*`, `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, and `>>>`, the comparisons `==`, `!=`, `<`, `≤`, `>`,
`≥`, `=`, and `≠` as `Bool` values, `!`, `&&`, and `||`, `if` on a `Bool` or on a comparison,
pairs built with `(a, b)` and taken apart with `.1`, `.2`, or `match`, `LeanExe.loop`,
`xs.size.toUInt64`, `xs[i.toNat]!`, `xs.set! i.toNat v`, `xs.push v`, `xs ++ ys`, `LeanExe.build`
of words, and calls of the listed definitions before it. -/

namespace Verified.Reflect

open Lean Meta Elab Command Term

partial def tyOf (type : Lean.Expr) : MetaM Ty := do
  let type ← whnfR type
  if type.isConstOf ``UInt64 then return .word
  if type.isConstOf ``Bool then return .bool
  if type.isConstOf ``Float then return .float
  if let (``Prod, #[a, b]) := type.getAppFnArgs then return .pair (← tyOf a) (← tyOf b)
  if let (``Array, #[e]) := type.getAppFnArgs then
    if (← whnfR e).isConstOf ``UInt64 then return .array
  throwError "verified_compile: the type {type} is not UInt64, Bool, Float, Array UInt64, or a pair"

def tyExpr : Ty → Lean.Expr
  | .word => mkConst ``Ty.word
  | .bool => mkConst ``Ty.bool
  | .pair a b => mkApp2 (mkConst ``Ty.pair) (tyExpr a) (tyExpr b)
  | .float => mkConst ``Ty.float
  | .array => mkConst ``Ty.array

def listExpr (α : Lean.Expr) : List Lean.Expr → Lean.Expr
  | [] => mkApp (mkConst ``List.nil [Level.zero]) α
  | x :: xs => mkApp3 (mkConst ``List.cons [Level.zero]) α x (listExpr α xs)

def ctxExpr (Γ : List Ty) : Lean.Expr := listExpr (mkConst ``Ty) (Γ.map tyExpr)

def modeExpr : Mode → Lean.Expr
  | .borrowed => mkConst ``Mode.borrowed
  | .owned => mkConst ``Mode.owned

def modesExpr (modes : List Mode) : Lean.Expr := listExpr (mkConst ``Mode) (modes.map modeExpr)

def sigExpr (params : List Ty) (result : Ty) (aborts : Bool) (modes : List Mode) : Lean.Expr :=
  mkApp4 (mkConst ``Sig.mk) (ctxExpr params) (tyExpr result) (toExpr aborts) (modesExpr modes)

/-- A listed definition that a later one may call: its name, its signature, whether a call may
trap, the modes of its parameters, and its equation `∀ args, Func.denote … = name args`. -/
structure Callee where
  name : Name
  params : List Ty
  result : Ty
  aborts : Bool
  modes : List Mode
  denoteEq : Name

/-- The functions an expression may call, the Lean functions they mean, the definitions behind
them, variable 0 of `sigs` first, the variables in scope with their types, variable 0 first, and
the environment of their values. -/
structure Ctx where
  sigs : Lean.Expr
  funs : Lean.Expr
  callees : List Callee
  vars : List (Lean.Expr × Ty)
  env : Lean.Expr

def Ctx.ctx (c : Ctx) : Lean.Expr := ctxExpr (c.vars.map (·.2))

/-- `Expr.denote funs e env`. -/
def denoteExpr (c : Ctx) (e : Lean.Expr) : MetaM Lean.Expr :=
  mkAppM ``Expr.denote #[c.funs, e, c.env]

/-- The proof by `rfl` that `e` means `lean`. -/
def rflProof (c : Ctx) (e lean : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl lean) (← mkEq (← denoteExpr c e) lean)

def binOp? : Name → Option Lean.Expr
  | ``HAdd.hAdd => some (mkConst ``BinOp.add)
  | ``HSub.hSub => some (mkConst ``BinOp.sub)
  | ``HMul.hMul => some (mkConst ``BinOp.mul)
  | ``HDiv.hDiv => some (mkConst ``BinOp.div)
  | ``HMod.hMod => some (mkConst ``BinOp.rem)
  | ``HAnd.hAnd => some (mkConst ``BinOp.and)
  | ``HOr.hOr => some (mkConst ``BinOp.or)
  | ``HXor.hXor => some (mkConst ``BinOp.xor)
  | ``HShiftLeft.hShiftLeft => some (mkConst ``BinOp.shl)
  | ``HShiftRight.hShiftRight => some (mkConst ``BinOp.shr)
  | _ => none

def fbinOp? : Name → Option Lean.Expr
  | ``HAdd.hAdd => some (mkConst ``FBinOp.add)
  | ``HSub.hSub => some (mkConst ``FBinOp.sub)
  | ``HMul.hMul => some (mkConst ``FBinOp.mul)
  | ``HDiv.hDiv => some (mkConst ``FBinOp.div)
  | _ => none

def isFloat (α : Lean.Expr) : MetaM Bool := return (← whnfR α).isConstOf ``Float

/-- A comparison of floats as a `Prop`: its operation and its operands, with `>` and `≥` as `<`
and `≤` on swapped operands.  `=` and `≠` on floats compare bit patterns, which `==` and `!=` do
not, and the reflector rejects them. -/
def fcomparison? (p : Lean.Expr) : MetaM (Option (FCmpOp × Lean.Expr × Lean.Expr)) := do
  match p.consumeMData.getAppFnArgs with
  | (``LT.lt, #[α, _, a, b]) => if ← isFloat α then return some (.lt, a, b) else return none
  | (``LE.le, #[α, _, a, b]) => if ← isFloat α then return some (.le, a, b) else return none
  | (``GT.gt, #[α, _, a, b]) => if ← isFloat α then return some (.lt, b, a) else return none
  | (``GE.ge, #[α, _, a, b]) => if ← isFloat α then return some (.le, b, a) else return none
  | (``Eq, #[α, _, _]) | (``Ne, #[α, _, _]) =>
    if ← isFloat α then
      throwError "verified_compile: = and ≠ on Float compare bit patterns; use == and !="
    return none
  | _ => return none

def fcmpExpr : FCmpOp → Lean.Expr
  | .lt => mkConst ``FCmpOp.lt
  | .le => mkConst ``FCmpOp.le
  | .eq => mkConst ``FCmpOp.eq

def natOf (n : Lean.Expr) : Option Nat := n.nat? <|> n.rawNatLit?

/-- The value of a word literal. -/
def wordLit? (e : Lean.Expr) : MetaM (Option UInt64) := do
  let (``OfNat.ofNat, #[α, n, _]) := e.consumeMData.getAppFnArgs | return none
  unless (← whnfR α).isConstOf ``UInt64 do return none
  return (natOf (← instantiateMVars n)).map UInt64.ofNat

/-- The bit pattern of a float literal: a scientific or natural literal, `Float.ofBits` or
`UInt64.toFloat` of a word literal, or the negation of a float literal.  Lean's model has one
NaN, so `Float.ofBits` and the negation give the canonical NaN for a NaN.  The kernel checks the
bits. -/
partial def floatLit? (e : Lean.Expr) : MetaM (Option UInt64) := do
  let canonical (w : UInt64) := if Wasm.IEEE64.isNaN w then Wasm.IEEE64.canonicalNaN else w
  match e.consumeMData.getAppFnArgs with
  | (``OfScientific.ofScientific, #[_, _, m, sgn, ex]) =>
    let some m := natOf (← instantiateMVars m) | return none
    let some ex := natOf (← instantiateMVars ex) | return none
    if sgn.isConstOf ``Bool.true then return some (Float.ofScientific m true ex).toBits
    if sgn.isConstOf ``Bool.false then return some (Float.ofScientific m false ex).toBits
    return none
  | (``OfNat.ofNat, #[_, n, _]) =>
    let some n := natOf (← instantiateMVars n) | return none
    return some (Float.ofNat n).toBits
  | (``Float.ofBits, #[w]) => return (← wordLit? w).map canonical
  | (``UInt64.toFloat, #[w]) => return (← wordLit? w).map Wasm.IEEE64.convertI64U
  | (``Neg.neg, #[_, _, x]) =>
    return (← floatLit? x).map fun b => canonical (b ^^^ 0x8000000000000000)
  | _ => return none

/-- A comparison of words as a `Prop`: its operation and its operands, with `>` and `≥` as `<`
and `≤` on swapped operands. -/
def comparison? (p : Lean.Expr) : MetaM (Option (CmpOp × Lean.Expr × Lean.Expr)) := do
  let p := p.consumeMData
  let isWord (α : Lean.Expr) : MetaM Bool := return (← whnfR α).isConstOf ``UInt64
  match p.getAppFnArgs with
  | (``LT.lt, #[α, _, a, b]) => if ← isWord α then return some (.lt, a, b) else return none
  | (``LE.le, #[α, _, a, b]) => if ← isWord α then return some (.le, a, b) else return none
  | (``GT.gt, #[α, _, a, b]) => if ← isWord α then return some (.lt, b, a) else return none
  | (``GE.ge, #[α, _, a, b]) => if ← isWord α then return some (.le, b, a) else return none
  | (``Eq, #[α, a, b]) => if ← isWord α then return some (.eq, a, b) else return none
  | (``Ne, #[α, a, b]) => if ← isWord α then return some (.ne, a, b) else return none
  | _ => return none

def cmpExpr : CmpOp → Lean.Expr
  | .eq => mkConst ``CmpOp.eq
  | .ne => mkConst ``CmpOp.ne
  | .lt => mkConst ``CmpOp.lt
  | .le => mkConst ``CmpOp.le

def iteLemma : CmpOp → Name
  | .eq => ``ite_eqP_eq
  | .ne => ``ite_ne_eq
  | .lt => ``ite_lt_eq
  | .le => ``ite_le_eq

/-- `Env.cons v₀ (… (Env.cons vₙ Env.nil))` for the variables `vars`. -/
def envExpr : List (Lean.Expr × Ty) → MetaM Lean.Expr
  | [] => return mkConst ``Env.nil
  | (x, t) :: rest => do
    mkAppOptM ``Env.cons
      #[some (ctxExpr (rest.map (·.2))), some (tyExpr t), some x, some (← envExpr rest)]

/-- `e` with each projection of a pair `(a, b)` at its head replaced by the component. -/
partial def projReduce (e : Lean.Expr) : Lean.Expr :=
  let e := e.consumeMData.headBeta
  match e.getAppFnArgs with
  | (``Prod.fst, #[_, _, p]) => match (projReduce p).getAppFnArgs with
    | (``Prod.mk, #[_, _, a, _]) => projReduce a
    | _ => e
  | (``Prod.snd, #[_, _, p]) => match (projReduce p).getAppFnArgs with
    | (``Prod.mk, #[_, _, _, b]) => projReduce b
    | _ => e
  | _ => e

/-- Whether a Lean term reflects to a place: a variable or a pair of places. -/
partial def isPlace (e : Lean.Expr) : Bool :=
  let e := projReduce e
  e.isFVar || match e.getAppFnArgs with
    | (``Prod.mk, #[_, _, a, b]) => isPlace a && isPlace b
    | _ => false

/-- `fn args`, with each argument that `bind` marks bound by a `let` around the application, in
order.  The result is equal to `fn args` by `zeta`. -/
def bindArgs (fn : Lean.Expr) : List Lean.Expr → List Bool → Array Lean.Expr → Array Lean.Expr →
    MetaM Lean.Expr
  | [], _, newArgs, fvars => mkLetFVars fvars (mkAppN fn newArgs)
  | a :: as, b :: bs, newArgs, fvars => do
    if b then
      withLetDecl `a (← inferType a) a fun x => bindArgs fn as bs (newArgs.push x) (fvars.push x)
    else bindArgs fn as bs (newArgs.push a) fvars
  | a :: as, [], newArgs, fvars => bindArgs fn as [] (newArgs.push a) fvars

/-- The source variable for the Lean variable `e` in scope, and its type. -/
def varOf (c : Ctx) (e : Lean.Expr) : MetaM (Lean.Expr × Ty) := do
  let some i := c.vars.findIdx? (·.1 == e)
    | throwError "verified_compile: {e} is not a variable in scope"
  let some (_, t) := c.vars[i]? | throwError "verified_compile: variable index {i}"
  let proof ← mkEqRefl (mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Ty) |>.app
    (tyExpr t))
  return (← mkAppOptM ``Var.ofIndex #[some (tyExpr t), some c.ctx, some (toExpr i), some proof],
    t)

/-- The source expression for the Lean term `e`, with the proof that it means `e`, and its
type.  An array that a reader reads and an argument with arrays that is not a place are bound
with `let` first.  A `let` of a place is replaced by its body with the place for the variable,
and every variable of a pair type is split into variables for its components, so that a
projection reads a component and a use of the whole is the pair of the components. -/
partial def reflect (c : Ctx) (e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
  let e := projReduce e
  if e.isFVar then
    let (x, t) ← varOf c e
    let src ← mkAppOptM ``Expr.var #[some c.sigs, some c.ctx, some (tyExpr t), some x]
    return (src, ← rflProof c src e, t)
  if let some src := ← reflectCall? e then return src
  if !e.hasFVar && !e.hasLooseBVars then
    match ← tyOf (← inferType e) with
    | .word =>
      let src ← mkAppOptM ``Expr.word #[some c.sigs, some c.ctx, some e]
      return (src, ← rflProof c src e, .word)
    | .bool =>
      let src ← mkAppOptM ``Expr.bool #[some c.sigs, some c.ctx, some e]
      return (src, ← rflProof c src e, .bool)
    | .float =>
      if let some bits ← floatLit? e then
        let src ← mkAppOptM ``Expr.float #[some c.sigs, some c.ctx, some (toExpr bits)]
        let prop ← mkEq (← mkAppM ``Float.toBits #[e]) (toExpr bits)
        let dec ← mkDecide prop
        let h := mkApp3 (mkConst ``of_decide_eq_true) prop dec.appArg!
          (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
        let proof ← mkAppOptM ``float_eq #[some c.sigs, some c.ctx, some c.funs, some c.env,
          some (toExpr bits), some e, some h]
        return (src, proof, .float)
    | .pair _ _ | .array => pure ()
  if let .letE _ type value body _ := e then
    if isPlace value then return ← reflect c (body.instantiate1 value)
    let s ← tyOf type
    if let .pair _ _ := s then
      return ← destructure c [] value fun a b => do
        return body.instantiate1 (← mkAppM ``Prod.mk #[a, b])
    let (vs, hv, _) ← reflect c value
    return ← withLocalDeclD `x type fun x => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (tyExpr s), some x, some c.env]
      let c' : Ctx := { c with vars := (x, s) :: c.vars, env := env' }
      let (bs, hb, t) ← reflect c' (body.instantiate1 x)
      let hb ← mkLambdaFVars #[x] hb
      let src ← mkAppM ``Expr.letE #[vs, bs]
      return (src, ← mkAppM ``letE_eq #[hv, hb], t)
  if let some app ← matchMatcherApp? e then
    if app.discrs.size == 1 && app.alts.size == 1 then
      let alt := app.alts[0]!
      if let (``Prod.mk, #[_, _, a, b]) := (projReduce app.discrs[0]!).getAppFnArgs then
        return ← reflect c (alt.beta #[a, b])
      return ← destructure c [] app.discrs[0]! fun a b => return alt.beta #[a, b]
  let (fn, args) := e.getAppFnArgs
  if let some op := binOp? fn then
    if args.size == 6 && (← isFloat args[0]!) then
      let some fop := fbinOp? fn
        | throwError "verified_compile: unsupported operation {fn} on Float"
      let (ls, hl, _) ← reflect c args[4]!
      let (rs, hr, _) ← reflect c args[5]!
      return (← mkAppM ``Expr.fbin #[fop, ls, rs], ← mkAppM ``fbin_eq #[fop, hl, hr], .float)
    if args.size == 6 then
      let (ls, hl, _) ← reflect c args[4]!
      let (rs, hr, _) ← reflect c args[5]!
      return (← mkAppM ``Expr.bin #[op, ls, rs], ← mkAppM ``bin_eq #[op, hl, hr], .word)
  match fn, args with
  | ``Decidable.decide, #[p, _] =>
    if let some (op, a, b) ← fcomparison? p then return ← reflectFCmp op a b
    let some (op, a, b) ← comparison? p
      | throwError "verified_compile: unsupported decision {p}"
    reflectCmp op a b
  | ``BEq.beq, #[α, _, a, b] =>
    if ← isFloat α then reflectFCmp .eq a b else reflectCmp .eq a b
  | ``bne, #[α, _, a, b] =>
    if ← isFloat α then
      let (s, h, _) ← reflectFCmp .eq a b
      return (← mkAppM ``Expr.not #[s], ← mkAppM ``not_eq #[h], .bool)
    reflectCmp .ne a b
  | ``Neg.neg, #[α, _, x] =>
    unless ← isFloat α do throwError "verified_compile: unsupported negation {e}"
    reflectFUnary (mkConst ``FUnOp.neg) x
  | ``Float.sqrt, #[x] => reflectFUnary (mkConst ``FUnOp.sqrt) x
  | ``UInt64.toFloat, #[x] =>
    reflectConv ``Expr.toFloat ``toFloat_eq (mkConst ``ToFloat.convert) x .float
  | ``Float.ofBits, #[x] =>
    reflectConv ``Expr.toFloat ``toFloat_eq (mkConst ``ToFloat.ofBits) x .float
  | ``Float.toUInt64, #[x] =>
    reflectConv ``Expr.toWord ``toWord_eq (mkConst ``ToWord.truncate) x .word
  | ``Float.toBits, #[x] => reflectConv ``Expr.toWord ``toWord_eq (mkConst ``ToWord.toBits) x .word
  | ``Float.abs, #[x] => reflectFUnary (mkConst ``FUnOp.abs) x
  | ``Min.min, #[α, inst, a, b] | ``Max.max, #[α, inst, a, b] =>
    unless ← isFloat α do throwError "verified_compile: unsupported {fn} on {α}"
    -- `min` and `max` are `if a ≤ b`, with operands that are not variables bound first.
    let bind := [false, false, !(projReduce a).isFVar, !(projReduce b).isFVar]
    if bind.any id then
      return ← reflect c (← bindArgs e.getAppFn [α, inst, a, b] bind #[] #[])
    let cond ← mkAppM ``LE.le #[a, b]
    let t ← if fn == ``Min.min then mkAppM ``ite #[cond, a, b] else mkAppM ``ite #[cond, b, a]
    let (src, proof, ty) ← reflect c t
    return (src, ← mkExpectedTypeHint proof (← mkEq (← denoteExpr c src) e), ty)
  | ``not, #[a] =>
    let (s, h, _) ← reflect c a
    return (← mkAppM ``Expr.not #[s], ← mkAppM ``not_eq #[h], .bool)
  | ``and, #[a, b] =>
    let (ls, hl, _) ← reflect c a
    let (rs, hr, _) ← reflect c b
    return (← mkAppM ``Expr.and #[ls, rs], ← mkAppM ``and_eq #[hl, hr], .bool)
  | ``or, #[a, b] =>
    let (ls, hl, _) ← reflect c a
    let (rs, hr, _) ← reflect c b
    return (← mkAppM ``Expr.or #[ls, rs], ← mkAppM ``or_eq #[hl, hr], .bool)
  | ``Prod.mk, #[_, _, a, b] =>
    let (as, ha, s) ← reflect c a
    let (bs, hb, t) ← reflect c b
    return (← mkAppM ``Expr.pair #[as, bs], ← mkAppM ``pair_eq #[ha, hb], .pair s t)
  | ``Prod.fst, #[_, _, p] => destructure c [] p fun a _ => return a
  | ``Prod.snd, #[_, _, p] => destructure c [] p fun _ b => return b
  | ``ite, #[_, p, _, a, b] =>
    let (as, ha, t) ← reflect c a
    let (bs, hb, _) ← reflect c b
    match (p.consumeMData).getAppFnArgs with
    | (``Eq, #[α, cond, tru]) =>
      if (← whnfR α).isConstOf ``Bool && tru.isConstOf ``Bool.true then
        let (cs, hc, _) ← reflect c cond
        return (← mkAppM ``Expr.ite #[cs, as, bs], ← mkAppM ``ite_eq #[hc, ha, hb], t)
    | _ => pure ()
    if let some (op, l, r) ← fcomparison? p then
      let (ls, hl, _) ← reflect c l
      let (rs, hr, _) ← reflect c r
      let cond ← mkAppM ``Expr.fcmp #[fcmpExpr op, ls, rs]
      let thm ← match op with
        | .lt => pure ``ite_flt_eq
        | .le => pure ``ite_fle_eq
        | .eq => throwError "verified_compile: unsupported condition {p}"
      return (← mkAppM ``Expr.ite #[cond, as, bs], ← mkAppM thm #[hl, hr, ha, hb], t)
    let some (op, l, r) ← comparison? p
      | throwError "verified_compile: unsupported condition {p}"
    let (ls, hl, _) ← reflect c l
    let (rs, hr, _) ← reflect c r
    let cond ← mkAppM ``Expr.cmp #[cmpExpr op, ls, rs]
    return (← mkAppM ``Expr.ite #[cond, as, bs], ← mkAppM (iteLemma op) #[hl, hr, ha, hb], t)
  | ``LeanExe.loop, #[α, n, init, f] =>
    let (ns, hn, _) ← reflect c n
    let (is, hi, t) ← reflect c init
    let (bs, hb, _) ← reflectUnder c [] (mkConst ``UInt64) α .word t fun i acc =>
      return f.beta #[i, acc]
    return (← mkAppM ``Expr.loop #[ns, is, bs], ← mkAppM ``loop_eq #[hn, hi, hb], t)
  | ``Array.set!, setArgs@#[α, xs, k, v] =>
    unless (← whnfR α).isConstOf ``UInt64 do
      throwError "verified_compile: only arrays of UInt64 are updated, in {e}"
    let (``UInt64.toNat, #[i]) := k.consumeMData.getAppFnArgs
      | throwError "verified_compile: a position must be `i.toNat` for a word `i`, in {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (setArgs.set! 1 a)))
    let (x, t) ← varOf c xs
    unless t == .array do throwError "verified_compile: {xs} is not an Array UInt64"
    let (is, hi, _) ← reflect c i
    let (vs, hv, _) ← reflect c v
    return (← mkAppOptM ``Expr.set #[some c.sigs, some c.ctx, some x, some is, some vs],
      ← mkAppM ``set_eq #[x, hi, hv], .array)
  | ``Array.push, pushArgs@#[α, xs, v] =>
    unless (← whnfR α).isConstOf ``UInt64 do
      throwError "verified_compile: only arrays of UInt64 are extended, in {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (pushArgs.set! 1 a)))
    let (x, t) ← varOf c xs
    unless t == .array do throwError "verified_compile: {xs} is not an Array UInt64"
    let (vs, hv, _) ← reflect c v
    return (← mkAppOptM ``Expr.push #[some c.sigs, some c.ctx, some x, some vs],
      ← mkAppM ``push_eq #[x, hv], .array)
  | ``HAppend.hAppend, appendArgs@#[α, _, _, _, xs, ys] =>
    unless (← tyOf α) == .array do throwError "verified_compile: unsupported term {e}"
    let xs := projReduce xs
    let ys := projReduce ys
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (appendArgs.set! 4 a)))
    unless ys.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType ys) ys fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (appendArgs.set! 5 a)))
    let (x, _) ← varOf c xs
    let (y, _) ← varOf c ys
    let src ← mkAppOptM ``Expr.append #[some c.sigs, some c.ctx, some x, some y]
    return (src, ← rflProof c src e, .array)
  | ``LeanExe.build, #[α, n, f] =>
    unless (← whnfR α).isConstOf ``UInt64 do
      throwError "verified_compile: only arrays of UInt64 are built, in {e}"
    let (ns, hn, _) ← reflect c n
    let (fs, hf) ← withLocalDeclD `i (mkConst ``UInt64) fun i => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (mkConst ``Ty.word), some i, some c.env]
      let c' : Ctx := { c with vars := (i, .word) :: c.vars, env := env' }
      let (fs, hf, t) ← reflect c' (f.beta #[i])
      unless t == .word do throwError "verified_compile: an element of {e} is not a UInt64"
      return (fs, ← mkLambdaFVars #[i] hf)
    return (← mkAppM ``Expr.build #[ns, fs], ← mkAppM ``build_eq #[hn, hf], .array)
  | ``Nat.toUInt64, #[n] =>
    let (``Array.size, sizeArgs@#[_, xs]) := n.consumeMData.getAppFnArgs
      | throwError "verified_compile: unsupported term {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn #[mkAppN n.consumeMData.getAppFn (sizeArgs.set! 1 a)]))
    let (x, t) ← varOf c xs
    unless t == .array do throwError "verified_compile: {xs} is not an Array UInt64"
    let src ← mkAppOptM ``Expr.size #[some c.sigs, some c.ctx, some x]
    return (src, ← rflProof c src e, .word)
  | ``getElem!, getArgs@#[_, _, _, _, _, _, xs, k] =>
    let (``UInt64.toNat, #[i]) := k.consumeMData.getAppFnArgs
      | throwError "verified_compile: an index must be `i.toNat` for a word `i`, in {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (getArgs.set! 6 a)))
    let (x, t) ← varOf c xs
    unless t == .array do throwError "verified_compile: {xs} is not an Array UInt64"
    let (is, hi, _) ← reflect c i
    return (← mkAppOptM ``Expr.get #[some c.sigs, some c.ctx, some x, some is],
      ← mkAppM ``get_eq #[x, hi], .word)
  | _, _ => throwError "verified_compile: unsupported term {e}"
where
  /-- The reflection of `body` in the context `c`, with each variable of `xs` that has a pair
  type split first into its components. -/
  reflectSplit (c : Ctx) : List Lean.Expr → Lean.Expr → MetaM (Lean.Expr × Lean.Expr × Ty)
    | [], body => reflect c body
    | x :: rest, body => do
      match ← tyOf (← inferType x) with
      | .pair _ _ =>
        destructure c rest x fun a b => do
          return body.replaceFVar x (← mkAppM ``Prod.mk #[a, b])
      | _ => reflectSplit c rest body
  /-- The reflection of `body a b` with `a : α` of type `s` as variable 1 and `b : β` of type `t`
  as variable 0, with its proof abstracted over `a` and `b`.  The variables `a`, `b`, and
  `rest` that have pair types are split. -/
  reflectUnder (c : Ctx) (rest : List Lean.Expr) (α β : Lean.Expr) (s t : Ty)
      (body : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) :=
    withLocalDeclD `a α fun a => withLocalDeclD `b β fun b => do
      let envA ← mkAppOptM ``Env.cons #[some c.ctx, some (tyExpr s), some a, some c.env]
      let ctxA := ctxExpr (s :: c.vars.map (·.2))
      let envB ← mkAppOptM ``Env.cons #[some ctxA, some (tyExpr t), some b, some envA]
      let c' : Ctx := { c with vars := (b, t) :: (a, s) :: c.vars, env := envB }
      let (bs, hb, u) ← reflectSplit c' (b :: a :: rest) (← body a b)
      return (bs, ← mkLambdaFVars #[a, b] hb, u)
  /-- The destructuring of the pair `p` into its components `a` and `b`, as variables 1 and 0
  of the body `body a b`, in which the variables `rest` are split. -/
  destructure (c : Ctx) (rest : List Lean.Expr) (p : Lean.Expr)
      (body : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (ps, hp, pt) ← reflect c p
    let .pair s t := pt | throwError "verified_compile: {p} is not a pair"
    let (``Prod, #[α, β]) := (← whnfR (← inferType p)).getAppFnArgs
      | throwError "verified_compile: {p} is not a pair"
    let (bs, hb, u) ← reflectUnder c rest α β s t body
    return (← mkAppM ``Expr.letPair #[ps, bs], ← mkAppM ``letPair_eq #[hp, hb], u)
  /-- A call of a listed definition before this one: the source call, with the proof built from
  the arguments' proofs and the callee's equation. -/
  reflectCall? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Ty)) := do
    let .const fn _ := e.getAppFn | return none
    let some j := c.callees.findIdx? (·.name == fn) | return none
    let some callee := c.callees[j]? | return none
    let args := e.getAppArgs
    unless args.size == callee.params.length do
      throwError "verified_compile: {fn} must be applied to all {callee.params.length} arguments"
    let bind := (args.toList.zip callee.params).zipIdx.map fun ((a, t), i) =>
      !t.scalar && if paramMode callee.params callee.modes i = .owned then !(projReduce a).isFVar
        else !isPlace a
    if bind.any id then
      return some (← reflect c (← bindArgs e.getAppFn args.toList bind #[] #[]))
    let reflected ← args.toList.mapM (reflect c)
    let nilArgs ← mkAppOptM ``Args.nil #[some c.sigs, some c.ctx]
    let argList ← reflected.foldrM (fun (s, _, _) acc => mkAppM ``Args.cons #[s, acc]) nilArgs
    let nilEq ← mkAppOptM ``ofFn_nil_eq #[some c.sigs, some c.ctx, some c.funs, some c.env]
    let hargs ← reflected.foldrM (fun (_, h, _) acc => mkAppM ``ofFn_cons_eq #[h, acc]) nilEq
    let values ← envExpr (args.toList.zip callee.params)
    let sig := sigExpr callee.params callee.result callee.aborts callee.modes
    let proof ← mkEqRefl (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Sig) sig)
    let f ← mkAppOptM ``FVar.ofIndex #[some sig, some c.sigs, some (toExpr j), some proof]
    let hf ← mkExpectedTypeHint (mkAppN (mkConst callee.denoteEq) args)
      (← mkEq (← mkAppM ``Funs.get #[c.funs, f, values]) e)
    let src ← mkAppM ``Expr.call #[f, ← mkAppM ``Args.get #[argList]]
    return some (src, ← mkAppM ``call_eq #[f, hargs, hf], callee.result)
  reflectCmp (op : CmpOp) (a b : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (ls, hl, _) ← reflect c a
    let (rs, hr, _) ← reflect c b
    return (← mkAppM ``Expr.cmp #[cmpExpr op, ls, rs], ← mkAppM ``cmp_eq #[cmpExpr op, hl, hr],
      .bool)
  reflectFCmp (op : FCmpOp) (a b : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (ls, hl, _) ← reflect c a
    let (rs, hr, _) ← reflect c b
    return (← mkAppM ``Expr.fcmp #[fcmpExpr op, ls, rs],
      ← mkAppM ``fcmp_eq #[fcmpExpr op, hl, hr], .bool)
  reflectFUnary (op x : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (s, h, _) ← reflect c x
    return (← mkAppM ``Expr.funary #[op, s], ← mkAppM ``funary_eq #[op, h], .float)
  reflectConv (ctor thm : Name) (op x : Lean.Expr) (t : Ty) :
      MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (s, h, _) ← reflect c x
    return (← mkAppM ctor #[op, s], ← mkAppM thm #[op, h], t)

/-- What the reflector learns from one definition: its signature, whether a call may trap, and the
modes of its parameters. -/
structure Reflected where
  name : Name
  params : List Ty
  result : Ty
  aborts : Bool
  modes : List Mode
  deriving Inhabited

def addDefinition (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addAndCompile <| .defnDecl <|
    mkDefinitionValEx name [] type value (.regular 1) .safe [name]

def addTheorem (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- The modes of a literal list of modes. -/
partial def modesOf (e : Lean.Expr) : Option (List Mode) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, m, rest]) =>
    let m? := if m.isConstOf ``Mode.owned then some Mode.owned
      else if m.isConstOf ``Mode.borrowed then some Mode.borrowed else none
    match m?, modesOf rest with
    | some m, some ms => some (m :: ms)
    | _, _ => none
  | _ => none

/-- Reflects definition `name` as a function that may call the functions `sigs`, meaning
`funs`, with the parameter modes that `Expr.paramChoice` gives, and adds `base.func` and
`base.denote_eq`. -/
def reflectDefinition (base name : Name) (sigs funs : Lean.Expr) (callees : List Callee) :
    MetaM Reflected := do
  let info ← getConstInfoDefn name
  unless info.levelParams.isEmpty do
    throwError "verified_compile: {name} has universe parameters"
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let types ← params.toList.mapM fun p => do tyOf (← inferType p)
    let result ← tyOf (← inferType body)
    let vars := params.toList.zip types
    let env ← envExpr vars
    let (src, proof, _) ← reflect.reflectSplit ⟨sigs, funs, callees, vars, env⟩ params.toList body
    let some modes := modesOf (← reduce (← mkAppM ``Expr.paramChoice #[src]))
      | throwError "verified_compile: cannot evaluate the parameter modes of {name}"
    let funcType := mkApp (mkConst ``Func) sigs
    let func ← mkAppOptM ``Func.mk #[some sigs, some (toExpr name.getString!),
      some (ctxExpr types), some (tyExpr result), some src, some (← mkEqRefl (toExpr true)),
      some (modesExpr modes)]
    addDefinition (base ++ `func) funcType func
    let lhs ← mkAppM ``Func.denote #[mkConst (base ++ `func), funs, env]
    let eqType ← mkForallFVars params (← mkEq lhs (mkAppN (mkConst name) params))
    addTheorem (base ++ `denote_eq) eqType (← mkLambdaFVars params proof)
    let aborts ← reduce (← mkAppM ``Func.aborts #[mkConst (base ++ `func)])
    unless aborts.isConstOf ``Bool.true || aborts.isConstOf ``Bool.false do
      throwError "verified_compile: cannot evaluate whether {name} may trap"
    return ⟨name, types, result, aborts.isConstOf ``Bool.true, modes⟩

def tyStx : Ty → CommandElabM Term
  | .word => `(UInt64)
  | .bool => `(Bool)
  | .pair a b => do `(($(← tyStx a) × $(← tyStx b)))
  | .array => `(Array UInt64)
  | .float => `(Float)

/-- The type of an argument in mode `m`: `Moved` for an owned array. -/
def argStx (t : Ty) : Mode → CommandElabM Term
  | .owned => do `(LeanExe.Pipeline.Moved $(← tyStx t))
  | .borrowed => tyStx t

/-- The argument type of a definition: its parameters' argument types as a right-nested product,
or `Unit` for none.  `modes` gives the parameters' modes. -/
def argType : List Ty → List Mode → CommandElabM Term
  | [], _ => `(Unit)
  | [t], m :: _ => argStx t m
  | [t], [] => tyStx t
  | t :: ts, ms => do
    `($(← argStx t (ms.headD .borrowed)) × $(← argType ts ms.tail))

def modeStx : Mode → CommandElabM Term
  | .owned => `(Verified.Mode.owned)
  | .borrowed => `(Verified.Mode.borrowed)

/-- The value of the argument `x` in mode `m`. -/
def argVal (x : Term) : Mode → CommandElabM Term
  | .owned => `($(x).val)
  | .borrowed => return x

/-- The values of the components of `x : argType params modes`, in order. -/
def argProjs (x : Term) : List Mode → Nat → CommandElabM (List Term)
  | _, 0 => return []
  | ms, 1 => return [← argVal x (ms.headD .borrowed)]
  | ms, n + 2 => do
    return (← argVal (← `($x.1)) (ms.headD .borrowed)) :: (← argProjs (← `($x.2)) ms.tail (n + 1))

/-- `FVar.there (… (FVar.there FVar.here))` with `k` applications of `there`. -/
def fvarStx : Nat → CommandElabM Term
  | 0 => `(Verified.FVar.here)
  | k + 1 => do `(Verified.FVar.there $(← fvarStx k))

syntax (name := verifiedCompile) "verified_compile " ident " := " "[" ident,* "]" : command

@[command_elab verifiedCompile]
def elabVerifiedCompile : CommandElab
  | `(verified_compile $target := [$sources,*]) => do
    let names ← sources.getElems.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let base := (← getCurrNamespace) ++ target.getId
    let reflected ← liftTermElabM do
      let mut sigs : List (List Ty × Ty × Bool × List Mode) := []
      let mut prog := Lean.mkConst ``Prog.nil
      let mut out : Array Reflected := #[]
      let mut callees : List Callee := []
      for name in names do
        let sigsExpr :=
          listExpr (Lean.mkConst ``Sig) (sigs.map fun (p, r, a, ms) => sigExpr p r a ms)
        let funs ← mkAppM ``Prog.funs #[prog]
        let fbase := base ++ Name.mkSimple name.getString!
        let r ← reflectDefinition fbase name sigsExpr funs callees
        prog ← mkAppM ``Prog.cons #[Lean.mkConst (fbase ++ `func), prog]
        sigs := (r.params, r.result, r.aborts, r.modes) :: sigs
        callees := ⟨name, r.params, r.result, r.aborts, r.modes, fbase ++ `denote_eq⟩ :: callees
        out := out.push r
      let sigsExpr :=
        listExpr (Lean.mkConst ``Sig) (sigs.map fun (p, r, a, ms) => sigExpr p r a ms)
      addDefinition (base ++ `program) (mkApp (Lean.mkConst ``Prog) sigsExpr) prog
      addDefinition (base ++ `module) (Lean.mkConst ``Wasm.Module)
        (← mkAppM ``compile #[Lean.mkConst (base ++ `program)])
      return out
    let progId := mkIdent (base ++ `program)
    let moduleId := mkIdent (base ++ `module)
    let n := reflected.size
    let mut claims : Array Term := #[]
    let mut proofs : Array Term := #[]
    for k in [0:n] do
      let r := reflected[k]!
      let simple := Name.mkSimple r.name.getString!
      let fnId := mkIdent r.name
      let implId := mkIdent (target.getId ++ simple ++ `implements)
      let eqId := mkIdent (base ++ simple ++ `denote_eq)
      let x := mkIdent `x
      let modes := paramModes r.params r.modes
      let α ← argType r.params modes
      let projs ← argProjs x modes r.params.length
      let chosen ← r.modes.toArray.mapM modeStx
      let fvar ← fvarStx (n - 1 - k)
      let index := Syntax.mkNumLit (toString (2 + k))
      let lean ← `(fun ($x : $α) => $fnId $(projs.toArray)*)
      let aborts := mkIdent (if r.aborts then ``Bool.true else ``Bool.false)
      elabCommand (← `(theorem $implId :
          LeanExe.Pipeline.ImplementsA $aborts $moduleId $index $lean (fun _ _ _ => True)
            (fun _ _ _ _ _ => True) := by
          have h := Verified.ImplementsA.lean (Verified.Prog.correct $progId $fvar).1
          have hComp : (fun $x => Verified.Funs.get (Verified.Prog.funs $progId) $fvar
              (Verified.Env.ofArgs _ [$chosen,*] $x)) = $lean := by
            funext $x
            exact $eqId $(projs.toArray)*
          rw [← hComp]
          exact h))
      claims := claims.push
        (← `(LeanExe.Pipeline.ImplementsA $aborts $(mkIdent `m) $index $lean (fun _ _ _ => True)
          (fun _ _ _ _ _ => True)))
      proofs := proofs.push implId
    let bytesId := mkIdent (target.getId ++ `bytes)
    let m := mkIdent `m
    let conj ← claims.pop.foldrM (fun c acc => `($c ∧ $acc)) claims.back!
    let impls ← proofs.pop.foldrM (fun p acc => `(⟨$p, $acc⟩)) proofs.back!
    elabCommand (← `(theorem $bytesId : ∃ bytes, Wasm.Encoding.encode $moduleId = .ok bytes ∧
        ∃ $m:ident, Wasm.Encoding.decode bytes = .ok $m ∧ $conj := by
      obtain ⟨bytes, success, decoded⟩ :=
        Wasm.Encoding.round_trip $moduleId (by decide) (by decide +kernel)
      exact ⟨bytes, success, $moduleId, decoded, $impls⟩))
  | _ => throwUnsupportedSyntax

end Verified.Reflect
