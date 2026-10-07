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
definition's parameters and result are `UInt64`, `Bool`, `Float`, structures with a `Flat` instance
whose tuple is their fields, arrays of `UInt64`, `Bool`, or `Float`, or pairs.  A structure's source
value is its flattening `φ`, the source value of its `Flat` tuple, and each equation states that the
source expression means `φ` of the Lean term, with `φ` the identity for the other types.  Its body
may use literals and other closed terms, its parameters, `let`, the word operations `+`, `-`,
`*`, `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, and `>>>`, the comparisons `==`, `!=`, `<`, `≤`, `>`,
`≥`, `=`, and `≠` as `Bool` values, `!`, `&&`, and `||`, `if` on a `Bool` or on a comparison,
pairs built with `(a, b)` and taken apart with `.1`, `.2`, or `match`, structures built with their
constructor or `{ s with … }` and taken apart with their fields or `match`, `LeanExe.loop`,
`xs.size.toUInt64`, `xs[i.toNat]!`, `xs.set! i.toNat v`, `xs.push v`, `xs ++ ys`, `LeanExe.build`
of words, and calls of the listed definitions before it. -/

namespace Verified.Reflect

open Lean Meta Elab Command Term

def elemOf? (type : Lean.Expr) : MetaM (Option Elem) := do
  let type ← whnfR type
  if type.isConstOf ``UInt64 then return some .word
  if type.isConstOf ``Bool then return some .bool
  if type.isConstOf ``Float then return some .float
  return none

/-- The element type of an array's elements of type `type`. -/
def elemOf (type : Lean.Expr) : MetaM Elem := do
  let some e ← elemOf? type
    | throwError "verified_compile: arrays hold UInt64, Bool, or Float, not {type}"
  return e

def elemExpr : Elem → Lean.Expr
  | .word => mkConst ``Elem.word
  | .bool => mkConst ``Elem.bool
  | .float => mkConst ``Elem.float
  | .prod a b => mkApp2 (mkConst ``Elem.prod) (elemExpr a) (elemExpr b)

/-- The path along the steps `steps`, from the outside in, of a component of an element of type
`e`: `false` for the first part and `true` for the second.  Also the component's type. -/
def pathExpr : Elem → List Bool → MetaM (Lean.Expr × Elem)
  | e, [] => return (mkApp (mkConst ``Path.here) (elemExpr e), e)
  | .prod a b, false :: rest => do
    let (p, t) ← pathExpr a rest
    return (mkApp4 (mkConst ``Path.fst) (elemExpr a) (elemExpr t) (elemExpr b) p, t)
  | .prod a b, true :: rest => do
    let (p, t) ← pathExpr b rest
    return (mkApp4 (mkConst ``Path.snd) (elemExpr b) (elemExpr t) (elemExpr a) p, t)
  | _, _ :: _ => throwError "verified_compile: a projection of an element that is not a tuple"

def tyExpr : Ty → Lean.Expr
  | .word => mkConst ``Ty.word
  | .bool => mkConst ``Ty.bool
  | .pair a b => mkApp2 (mkConst ``Ty.pair) (tyExpr a) (tyExpr b)
  | .float => mkConst ``Ty.float
  | .elem e => mkApp (mkConst ``Ty.elem) (elemExpr e)
  | .array e => mkApp (mkConst ``Ty.array) (elemExpr e)

/-- How a Lean type is flattened into a source type: the source type, and the function `φ` from
the Lean type to the source type's meaning, `none` for the identity.  A structure with a `Flat`
instance is the flattening of its `Flat` tuple, so nested structures are flattened in turn. -/
structure Shape where
  ty : Ty
  flat : Option Lean.Expr

/-- `φ e`, beta-reduced. -/
def Shape.apply (sh : Shape) (e : Lean.Expr) : Lean.Expr :=
  match sh.flat with
  | none => e
  | some f => f.beta #[e]

/-- `φ` as a function from `type` to the source type's meaning, the identity when `flat` is
`none`. -/
def Shape.fn (sh : Shape) (type : Lean.Expr) : MetaM Lean.Expr := do
  let f ← match sh.flat with
    | some f => pure f
    | none => withLocalDeclD `x type fun x => mkLambdaFVars #[x] x
  mkExpectedTypeHint f (← mkArrow type (mkApp (mkConst ``Ty.denote) (tyExpr sh.ty)))

/-- The `Flat` instance of a type and its tuple type, if Lean finds one. -/
def flatInstance? (type : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let β ← mkFreshTypeMVar
  let some inst ← synthInstance? (mkApp2 (mkConst ``LeanExe.Pipeline.Flat) type β)
    | return none
  return some (← instantiateMVars β, inst)

partial def shapeOf (type : Lean.Expr) : MetaM Shape := do
  if let some e ← elemOf? type then return ⟨.elem e, none⟩
  let type ← whnfR type
  if let (``Prod, #[a, b]) := type.getAppFnArgs then
    let sa ← shapeOf a
    let sb ← shapeOf b
    let ty := match sa.ty, sb.ty with
      | .elem ea, .elem eb => Ty.elem (.prod ea eb)
      | ta, tb => .pair ta tb
    if sa.flat.isNone && sb.flat.isNone then return ⟨ty, none⟩
    let f ← withLocalDeclD `p type fun p => do
      mkLambdaFVars #[p] (← mkAppM ``Prod.mk
        #[sa.apply (← mkAppM ``Prod.fst #[p]), sb.apply (← mkAppM ``Prod.snd #[p])])
    return ⟨ty, some f⟩
  if let (``Array, #[el]) := type.getAppFnArgs then
    let se ← shapeOf el
    let .elem e := se.ty | throwError "verified_compile: an array holds elements, not {el}"
    unless se.flat.isNone do
      throwError "verified_compile: arrays of structures are not supported yet: {type}"
    return ⟨.array e, none⟩
  if let some (β, inst) ← flatInstance? type then
    let sβ ← shapeOf β
    let .elem _ := sβ.ty | throwError "verified_compile: the structure {type} holds arrays"
    let f ← withLocalDeclD `x type fun x => do
      mkLambdaFVars #[x] (sβ.apply (mkApp4 (mkConst ``LeanExe.Pipeline.Flat.flat) type β inst x))
    return ⟨sβ.ty, some f⟩
  throwError "verified_compile: the type {type} is not UInt64, Bool, Float, a structure with a \
    `Flat` instance, an array, or a pair"

def tyOf (type : Lean.Expr) : MetaM Ty := return (← shapeOf type).ty

/-- The constructor and field names of a structure type other than `Prod`. -/
def structOf? (type : Lean.Expr) : MetaM (Option (ConstructorVal × Array Name)) := do
  let type ← whnfR type
  let .const n _ := type.getAppFn | return none
  if n == ``Prod then return none
  let env ← getEnv
  unless isStructure env n do return none
  let some (.ctorInfo ctor) := env.find? (getStructureCtor env n).name | return none
  return some (ctor, getStructureFields env n)

/-- The tuple tree of a structure's `Flat` instance: `Flat.flat` of the structure built from fresh
variables, reduced down the tuple's pairs, has those variables at its leaves.  Each leaf is the
index of a field, and a leaf is reached by steps `false` for a pair's first component and `true`
for its second.  The reflector rejects an instance whose leaves are not distinct fields. -/
partial def flatTree (type β inst : Lean.Expr) (ctor : ConstructorVal) :
    MetaM (List (Nat × List Bool)) := do
  let type ← whnfR type
  let ctorApp := mkAppN (mkConst ctor.name type.getAppFn.constLevels!) type.getAppArgs
  forallBoundedTelescope (← inferType ctorApp) ctor.numFields fun ys _ => do
    let t := mkApp4 (mkConst ``LeanExe.Pipeline.Flat.flat) type β inst (mkAppN ctorApp ys)
    let rec descend (t ty : Lean.Expr) (steps : List Bool) : MetaM (List (Nat × List Bool)) := do
      let ty ← whnfR ty
      let t' ← whnf t
      if let some i := ys.findIdx? (· == t') then return [(i, steps.reverse)]
      if let (``Prod, #[a, b]) := ty.getAppFnArgs then
        if let (``Prod.mk, #[_, _, x, y]) := t'.getAppFnArgs then
          return (← descend x a (false :: steps)) ++ (← descend y b (true :: steps))
      throwError "verified_compile: the `Flat` instance of {type} is not a tuple of its fields"
    let leaves ← descend t β []
    unless (leaves.map (·.1)).eraseDups.length == leaves.length do
      throwError "verified_compile: the `Flat` instance of {type} repeats a field"
    return leaves

/-- The steps to field `i` of a structure value in its flattening, if the type is a structure
with a `Flat` instance. -/
def fieldPath? (type : Lean.Expr) (i : Nat) : MetaM (Option (List Bool)) := do
  let some (ctor, _) ← structOf? type | return none
  let some (β, inst) ← flatInstance? type | return none
  let tree ← flatTree type β inst ctor
  return (tree.find? (·.1 == i)).map (·.2)

/-- Field `i` and the structure value `p` of a structure projection `e`. -/
def structProj? (e : Lean.Expr) : MetaM (Option (Nat × Lean.Expr)) := do
  if let .proj _ i p := e then return some (i, p)
  let .const fn _ := e.getAppFn | return none
  let some info ← getProjectionFnInfo? fn | return none
  if info.fromClass then return none
  let args := e.getAppArgs
  unless args.size == info.numParams + 1 do return none
  return some (info.i, args[info.numParams]!)

/-- The source value of a Lean term: its flattening. -/
def flatValue (e : Lean.Expr) : MetaM Lean.Expr := return (← shapeOf (← inferType e)).apply e

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
      #[some (ctxExpr (rest.map (·.2))), some (tyExpr t), some (← flatValue x),
        some (← envExpr rest)]

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
    return (src, ← rflProof c src (← flatValue e), t)
  if let some src := ← reflectCall? e then return src
  if let some src := ← reflectStruct? e then return src
  let shape ← shapeOf (← inferType e)
  if !e.hasFVar && !e.hasLooseBVars && shape.flat.isNone then
    match shape.ty with
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
    | .elem (.prod _ _) | .pair _ _ | .array _ => pure ()
  if let .letE _ type value body _ := e then
    if isPlace value then return ← reflect c (body.instantiate1 value)
    let s ← tyOf type
    if let .pair _ _ := s then
      return ← destructure c [] value fun a b => do
        return body.instantiate1 (← mkAppM ``Prod.mk #[a, b])
    let (vs, hv, _) ← reflect c value
    let sv ← shapeOf type
    return ← withLocalDeclD `x type fun x => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (tyExpr s), some (sv.apply x), some c.env]
      let c' : Ctx := { c with vars := (x, s) :: c.vars, env := env' }
      let (bs, hb, t) ← reflect c' (body.instantiate1 x)
      let hb ← mkLambdaFVars #[x] hb
      let src ← mkAppM ``Expr.letE #[vs, bs]
      if sv.flat.isNone then return (src, ← mkAppM ``letE_eq #[hv, hb], t)
      return (src, ← mkAppM ``letE_flat_eq #[← sv.fn type, value, hv, hb], t)
  if let some app ← matchMatcherApp? e then
    if app.discrs.size == 1 && app.alts.size == 1 then
      let alt := app.alts[0]!
      let d := app.discrs[0]!
      if let (``Prod.mk, #[_, _, a, b]) := (projReduce d).getAppFnArgs then
        return ← reflect c (alt.beta #[a, b])
      if let some (_, fields) ← structOf? (← inferType d) then
        -- The fields of a structure are its projections, of a variable bound to it first.
        let fieldsOf (y : Lean.Expr) : MetaM (Array Lean.Expr) := fields.mapM (mkProjection y)
        if (projReduce d).isFVar then return ← reflect c (alt.beta (← fieldsOf d))
        return ← reflect c (← withLetDecl `t (← inferType d) d fun y => do
          mkLetFVars #[y] (alt.beta (← fieldsOf y)))
      if let .elem _ ← tyOf (← inferType d) then
        -- The components of a tuple are its projections, of a variable bound to it first.
        if (projReduce d).isFVar then
          return ← reflect c (alt.beta #[← mkAppM ``Prod.fst #[d], ← mkAppM ``Prod.snd #[d]])
        return ← reflect c (← withLetDecl `t (← inferType d) d fun y => do
          mkLetFVars #[y] (alt.beta #[← mkAppM ``Prod.fst #[y], ← mkAppM ``Prod.snd #[y]]))
      return ← destructure c [] d fun a b => return alt.beta #[a, b]
  if let some (_, p) ← structProj? e then
    if (← structOf? (← inferType p)).isSome then return ← reflectProj e
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
    if let (.elem ea, .elem eb) := (s, t) then
      return (← mkAppM ``Expr.mk #[as, bs], ← mkAppM ``mk_eq #[ha, hb], .elem (.prod ea eb))
    return (← mkAppM ``Expr.pair #[as, bs], ← mkAppM ``pair_eq #[ha, hb], .pair s t)
  | ``Prod.fst, #[_, _, p] =>
    if let .elem _ ← tyOf (← inferType p) then reflectProj e
    else destructure c [] p fun a _ => return a
  | ``Prod.snd, #[_, _, p] =>
    if let .elem _ ← tyOf (← inferType p) then reflectProj e
    else destructure c [] p fun _ b => return b
  | ``ite, #[α, p, inst, a, b] =>
    let (src, proof, t) ← reflectIte p a b
    let some φ := (← shapeOf α).flat | return (src, proof, t)
    -- The `if` of the flattenings is the flattening of the `if`.
    let comm ← mkAppOptM ``apply_ite #[none, none, some φ, some p, some inst, some a, some b]
    return (src, ← mkEqTrans proof (← mkEqSymm comm), t)
  | ``LeanExe.loop, #[α, n, init, f] =>
    let (ns, hn, _) ← reflect c n
    let (is, hi, t) ← reflect c init
    let (bs, hb, _) ← reflectUnder c [] (mkConst ``UInt64) α .word t fun i acc =>
      return f.beta #[i, acc]
    let sa ← shapeOf α
    if sa.flat.isNone then
      return (← mkAppM ``Expr.loop #[ns, is, bs], ← mkAppM ``loop_eq #[hn, hi, hb], t)
    return (← mkAppM ``Expr.loop #[ns, is, bs],
      ← mkAppM ``loop_flat_eq #[← sa.fn α, init, f, hn, hi, hb], t)
  | ``Array.set!, setArgs@#[α, xs, k, v] =>
    let el ← elemOf α
    let (``UInt64.toNat, #[i]) := k.consumeMData.getAppFnArgs
      | throwError "verified_compile: a position must be `i.toNat` for a word `i`, in {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (setArgs.set! 1 a)))
    let (x, t) ← varOf c xs
    unless t == .array el do throwError "verified_compile: {xs} is not an array variable"
    let (is, hi, _) ← reflect c i
    let (vs, hv, _) ← reflect c v
    return (← mkAppOptM ``Expr.set #[some c.sigs, some c.ctx, none, some x, some is, some vs],
      ← mkAppM ``set_eq #[x, hi, hv], .array el)
  | ``Array.push, pushArgs@#[α, xs, v] =>
    let el ← elemOf α
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (pushArgs.set! 1 a)))
    let (x, t) ← varOf c xs
    unless t == .array el do throwError "verified_compile: {xs} is not an array variable"
    let (vs, hv, _) ← reflect c v
    return (← mkAppOptM ``Expr.push #[some c.sigs, some c.ctx, none, some x, some vs],
      ← mkAppM ``push_eq #[x, hv], .array el)
  | ``HAppend.hAppend, appendArgs@#[α, _, _, _, xs, ys] =>
    let .array el ← tyOf α | throwError "verified_compile: unsupported term {e}"
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
    let src ← mkAppOptM ``Expr.append #[some c.sigs, some c.ctx, none, some x, some y]
    return (src, ← rflProof c src e, .array el)
  | ``LeanExe.build, #[α, n, f] =>
    let el ← elemOf α
    let (ns, hn, _) ← reflect c n
    let (fs, hf) ← withLocalDeclD `i (mkConst ``UInt64) fun i => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (mkConst ``Ty.word), some i, some c.env]
      let c' : Ctx := { c with vars := (i, .word) :: c.vars, env := env' }
      let (fs, hf, t) ← reflect c' (f.beta #[i])
      unless t == .elem el do throwError "verified_compile: an element of {e} is not a {α}"
      return (fs, ← mkLambdaFVars #[i] hf)
    return (← mkAppM ``Expr.build #[ns, fs], ← mkAppM ``build_eq #[hn, hf], .array el)
  | ``Nat.toUInt64, #[n] =>
    let (``Array.size, sizeArgs@#[_, xs]) := n.consumeMData.getAppFnArgs
      | throwError "verified_compile: unsupported term {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn #[mkAppN n.consumeMData.getAppFn (sizeArgs.set! 1 a)]))
    let (x, t) ← varOf c xs
    let .array _ := t | throwError "verified_compile: {xs} is not an array variable"
    let src ← mkAppOptM ``Expr.size #[some c.sigs, some c.ctx, none, some x]
    return (src, ← rflProof c src e, .word)
  | ``getElem!, getArgs@#[_, _, _, _, _, _, xs, k] =>
    let (``UInt64.toNat, #[i]) := k.consumeMData.getAppFnArgs
      | throwError "verified_compile: an index must be `i.toNat` for a word `i`, in {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflect c (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (getArgs.set! 6 a)))
    let (x, t) ← varOf c xs
    let .array el := t | throwError "verified_compile: {xs} is not an array variable"
    let (is, hi, _) ← reflect c i
    return (← mkAppOptM ``Expr.get #[some c.sigs, some c.ctx, none, some x, some is],
      ← mkAppM ``get_eq #[x, hi], .elem el)
  | _, _ => throwError "verified_compile: unsupported term {e}"
where
  /-- A structure built with its constructor: the tuple that its `Flat` instance makes of the
  fields, reflected as a tuple, whose meaning is the structure's flattening. -/
  reflectStruct? (e : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Ty)) := do
    let .const ctorName _ := e.getAppFn | return none
    let some (.ctorInfo ctor) := (← getEnv).find? ctorName | return none
    let type ← inferType e
    let some (ctor', _) ← structOf? type | return none
    unless ctor'.name == ctor.name do return none
    let args := e.getAppArgs
    unless args.size == ctor.numParams + ctor.numFields do return none
    let some (β, inst) ← flatInstance? type | return none
    let tree ← flatTree type β inst ctor
    let fields := args.extract ctor.numParams args.size
    -- The tuple of the fields along the tree.
    let rec build (pre : List Bool) (ty : Lean.Expr) : MetaM Lean.Expr := do
      if let some (i, _) := tree.find? (·.2 == pre.reverse) then return fields[i]!
      let ty ← whnfR ty
      let (``Prod, #[a, b]) := ty.getAppFnArgs
        | throwError "verified_compile: the `Flat` instance of {type} is not a tuple of its fields"
      mkAppM ``Prod.mk #[← build (false :: pre) a, ← build (true :: pre) b]
    let tuple ← build [] β
    let (src, proof, t) ← reflect c tuple
    return some (src, ← mkExpectedTypeHint proof (← mkEq (← denoteExpr c src) (← flatValue e)), t)
  /-- An `if` on the condition `p` between `a` and `b`, whose meaning is the `if` of their
  flattenings. -/
  reflectIte (p a b : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
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
      let envA ← mkAppOptM ``Env.cons
        #[some c.ctx, some (tyExpr s), some (← flatValue a), some c.env]
      let ctxA := ctxExpr (s :: c.vars.map (·.2))
      let envB ← mkAppOptM ``Env.cons
        #[some ctxA, some (tyExpr t), some (← flatValue b), some envA]
      let c' : Ctx := { c with vars := (b, t) :: (a, s) :: c.vars, env := envB }
      let (bs, hb, u) ← reflectSplit c' (b :: a :: rest) (← body a b)
      return (bs, ← mkLambdaFVars #[a, b] hb, u)
  /-- A component of a tuple, `e`, a chain of `Prod.fst` and `Prod.snd`: the projection of a tuple
  variable along a path, with a tuple that is not a variable bound with `let` first. -/
  reflectProj (e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let rec walk (e : Lean.Expr) (steps : List Bool) : MetaM (Lean.Expr × List Bool) := do
      let e := projReduce e
      match e.getAppFnArgs with
      | (``Prod.fst, #[_, _, p]) =>
        if let .elem _ ← tyOf (← inferType p) then walk p (false :: steps) else return (e, steps)
      | (``Prod.snd, #[_, _, p]) =>
        if let .elem _ ← tyOf (← inferType p) then walk p (true :: steps) else return (e, steps)
      | _ =>
        let some (i, p) ← structProj? e | return (e, steps)
        let some path ← fieldPath? (← inferType p) i | return (e, steps)
        walk p (path ++ steps)
    let (base, steps) ← walk e []
    if base.isFVar then
      let (x, t) ← varOf c base
      let .elem be := t | throwError "verified_compile: {base} is not a tuple"
      let (path, target) ← pathExpr be steps
      let src ← mkAppOptM ``Expr.proj #[some c.sigs, some c.ctx, some (elemExpr be),
        some (elemExpr target), some x, some path]
      return (src, ← rflProof c src (← flatValue e), .elem target)
    reflect c (← withLetDecl `t (← inferType base) base fun y => do
      let chain ← steps.foldlM (fun acc step =>
        mkAppM (if step then ``Prod.snd else ``Prod.fst) #[acc]) y
      mkLetFVars #[y] chain)
  /-- The destructuring of the pair `p` into its components `a` and `b`, as variables 1 and 0
  of the body `body a b`, in which the variables `rest` are split. -/
  destructure (c : Ctx) (rest : List Lean.Expr) (p : Lean.Expr)
      (body : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (ps, hp, pt) ← reflect c p
    let .pair s t := pt | throwError "verified_compile: {p} is not a pair"
    let (``Prod, #[α, β]) := (← whnfR (← inferType p)).getAppFnArgs
      | throwError "verified_compile: {p} is not a pair"
    let (bs, hb, u) ← reflectUnder c rest α β s t body
    let sa ← shapeOf α
    let sb ← shapeOf β
    if sa.flat.isNone && sb.flat.isNone then
      return (← mkAppM ``Expr.letPair #[ps, bs], ← mkAppM ``letPair_eq #[hp, hb], u)
    return (← mkAppM ``Expr.letPair #[ps, bs],
      ← mkAppM ``letPair_flat_eq #[← sa.fn α, ← sb.fn β, p, hp, hb], u)
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
      (← mkEq (← mkAppM ``Funs.get #[c.funs, f, values]) (← flatValue e))
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
  /-- The Lean type of the tuple of the definition's arguments, with `Moved` for an owned array. -/
  argsType : Lean.Expr
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
    let resultShape ← shapeOf (← inferType body)
    let result := resultShape.ty
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
    let eqType ← mkForallFVars params
      (← mkEq lhs (resultShape.apply (mkAppN (mkConst name) params)))
    addTheorem (base ++ `denote_eq) eqType (← mkLambdaFVars params proof)
    let aborts ← reduce (← mkAppM ``Func.aborts #[mkConst (base ++ `func)])
    unless aborts.isConstOf ``Bool.true || aborts.isConstOf ``Bool.false do
      throwError "verified_compile: cannot evaluate whether {name} may trap"
    -- The flattenings of the tuple of the arguments and of the result, which the theorem uses.
    let pModes := paramModes types modes
    let argTys ← (params.toList.zip pModes).mapM fun (p, m) => do
      let ty ← inferType p
      return (p, if m == .owned then mkApp (mkConst ``LeanExe.Pipeline.Moved) ty else ty)
    let argsType ← tupleType (argTys.map (·.2))
    let plain ← params.toList.allM fun p => do return (← shapeOf (← inferType p)).flat.isNone
    let flatArgs ← withLocalDeclD `x argsType fun x => do
      mkLambdaFVars #[x] (← if plain then pure x else flatTuple x (argTys.map (·.1)))
    addDefinition (base ++ `flatArgs)
      (← mkArrow argsType (← mkAppM ``argsTy #[ctxExpr types, modesExpr modes])) flatArgs
    addDefinition (base ++ `flatResult)
      (← mkArrow (← inferType body) (← mkAppM ``Ty.denote #[tyExpr result]))
      (← resultShape.fn (← inferType body))
    return ⟨name, types, result, aborts.isConstOf ``Bool.true, modes, argsType⟩
where
  /-- The right-nested product of `tys`, `Unit` for none. -/
  tupleType : List Lean.Expr → MetaM Lean.Expr
    | [] => return mkConst ``Unit
    | [t] => return t
    | t :: ts => do mkAppM ``Prod #[t, ← tupleType ts]
  /-- The tuple of the flattenings of the components of `x`, a value of `tupleType` of the
  parameters' types; an owned array's component is its own flattening, the identity. -/
  flatTuple (x : Lean.Expr) : List Lean.Expr → MetaM Lean.Expr
    | [] => return mkConst ``Unit.unit
    | [p] => do
      if (← inferType x) == (← inferType p) then flatValue x else return x
    | p :: ps => do
      let first ← mkAppM ``Prod.fst #[x]
      let rest ← mkAppM ``Prod.snd #[x]
      let f ← if (← inferType first) == (← inferType p) then flatValue first else pure first
      mkAppM ``Prod.mk #[f, ← flatTuple rest ps]

/-- The value of the argument `x` in mode `m`. -/
def argVal (x : Term) : Mode → CommandElabM Term
  | .owned => `($(x).val)
  | .borrowed => return x

/-- The values of the components of `x`, the tuple of a definition's arguments, in order. -/
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
      let α ← liftTermElabM <| withOptions (fun o => o.setBool `pp.fullNames true) <|
        PrettyPrinter.delab r.argsType
      let projs ← argProjs x modes r.params.length
      let fvar ← fvarStx (n - 1 - k)
      let index := Syntax.mkNumLit (toString (2 + k))
      let lean ← `(fun ($x : $α) => $fnId $(projs.toArray)*)
      let aborts := mkIdent (if r.aborts then ``Bool.true else ``Bool.false)
      let flatArgs := mkIdent (base ++ simple ++ `flatArgs)
      let flatResult := mkIdent (base ++ simple ++ `flatResult)
      -- The theorem for the flattened types, carried to Lean's types: each argument is
      -- represented as its flattening is, and the flattening of the result represents it.
      elabCommand (← `(theorem $implId :
          LeanExe.Pipeline.ImplementsA $aborts $moduleId $index $lean (fun _ _ _ => True)
            (fun _ _ _ _ _ => True) := by
          have h := Verified.ImplementsA.lean (Verified.Prog.correct $progId $fvar).1
          refine Verified.ImplementsA.transferFlat h $flatArgs $flatResult $lean ?_ ?_ ?_ ?_ ?_ ?_
          · intro $x:ident; exact $eqId $(projs.toArray)*
          · intro _ _ _ _ hy; exact hy
          · intro _ _ _ _ _ hs; exact hs
          · intro _ _ _ _ _; rfl
          · intro _ _ _ _ hz; exact hz
          · intro _ _ _; rfl))
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
