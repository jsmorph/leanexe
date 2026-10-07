import Verified.Correct
import Verified.Reflect.Lemmas
import Verified.Reflect.Modes
import LeanExe.Encoding.RoundTrip

/-! The reflector.  `verified_compile p := [f, g, …]` reads the listed Lean definitions, writes
each as a source function, and proves its equation `denote (reflect f) = f` from the lemmas of
`Verified.Reflect.Lemmas`, composed term by term.  It adds the program `p.program`, the meanings
`p.funs` of its functions with the proof `p.meaning` that they are, the module
`p.module := compile p.program`, in which the `k`-th definition is function `2 + k`, and for each
definition `f` the source function `p.f.func`, the equation `p.f.denote_eq`, and the theorem
`p.f.implements` that the module computes `f`, at the entry of `f` when its code takes the call
depth.  A recursive definition is reflected from its unfolding equation, and its meaning
`p.f.meaning` is the definition at the inverses of the flattenings.  `p.bytes` states that the
module's bytes decode to the module, which computes every listed definition.

The reflector is meta code and is not trusted: Lean's kernel checks every equation it builds, and
the theorem holds for the parameter modes that `Expr.paramChoice` chooses as for any others.  A
definition's parameters and result are `UInt64`, `Bool`, `Float`, structures with a `Flat` instance
whose tuple is their fields, enumerations with a `Flat` instance to words, arrays of these, and
pairs.  Its body may also hold arrays of tuples, which have no `Represent` instance.  A structure's
source value is its flattening `φ`, the source value of its `Flat` tuple, an array's is the array of
its elements' flattenings, and each equation states that the source expression means `φ` of the Lean
term, with `φ` the identity for the types without structures.  The theorem follows from the equation
by `ImplementsA.transferAgree`, with proofs that Lean's instances agree with the source instances
along `φ`.  Its body may use literals, its parameters, `let`, the word operations `+`, `-`, `*`,
`/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, and `>>>`, the comparisons `==`, `!=`, `<`, `≤`, `>`, `≥`,
`=`, and `≠` as `Bool` values, `!`, `&&`, and `||`, `if` on a `Bool` or on a comparison, also as
`if h : c` with branches that do not use `h`, pairs built
with `(a, b)` and taken apart with `.1`, `.2`, or `match`, structures built with their constructor
or `{ s with … }` and taken apart with their fields or `match`, enumeration constructors,
`Flat.flat` of enumerations, `match` on enumerations, and `==`, `!=`, `decide`, and `if` on them,
`LeanExe.loop`, `LeanExe.repeatWhile`, `xs.size.toUInt64`, `xs[i.toNat]!`, `xs.set! i.toNat v`,
`xs.push v`, `xs ++ ys`, `LeanExe.build`, calls of the listed definitions before it, and, in a
recursive definition, calls of itself. -/

namespace Verified.Reflect

open Lean Meta Elab Command Term

def elemOf? (type : Lean.Expr) : MetaM (Option Elem) := do
  let type ← whnfR type
  if type.isConstOf ``UInt64 then return some .word
  if type.isConstOf ``Bool then return some .bool
  if type.isConstOf ``Float then return some .float
  return none

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
    if se.flat.isNone then return ⟨.array e, none⟩
    let φ ← se.fn el
    let f ← withLocalDeclD `xs type fun xs => do mkLambdaFVars #[xs] (← mkAppM ``Array.map #[φ, xs])
    return ⟨.array e, some f⟩
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

def sigExpr (g : Sig) : Lean.Expr :=
  mkApp5 (mkConst ``Sig.mk) (ctxExpr g.params) (tyExpr g.result) (toExpr g.aborts)
    (modesExpr g.modes) (toExpr g.depth)

/-- A listed definition that a later one may call: its name, its signature, and its equation
`∀ args, Func.denote … = name args`. -/
structure Callee where
  name : Name
  sig : Sig
  denoteEq : Name

/-- The functions an expression may call, the Lean functions they mean, the definitions behind
them, variable 0 of `sigs` first, the variables in scope with their types, variable 0 first, and
the environment of their values. -/
structure Ctx where
  /-- The program's name, under which the reflector adds the theorems it shares between
  definitions. -/
  base : Name
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

/-- `Eq.trans p q` with the middle term of `p`.  The elaborator does not unify the two middle
terms; the kernel checks that `q`'s left side is the same term, which the reflector arranges up to
beta reduction. -/
def transHint (p q : Lean.Expr) : MetaM Lean.Expr := do
  let some (α, a, b) := (← inferType p).eq? | throwError "verified_compile: the equation {p}"
  let some (_, _, c) := (← inferType q).eq? | throwError "verified_compile: the equation {q}"
  return mkApp6 (mkConst ``Eq.trans [← getLevel α]) α a b c p
    (← mkExpectedTypeHint q (← mkEq b c))

/-- The reference to function `j` of the signatures `sigs`, a list of `Sig` literals, as a chain
of `FVar.there` around `FVar.here`. -/
partial def fvarAt (sigs : Lean.Expr) (j : Nat) : MetaM Lean.Expr := do
  let (``List.cons, #[_, h, rest]) := sigs.getAppFnArgs
    | throwError "verified_compile: no function {j} in {sigs}"
  if j == 0 then return mkApp2 (mkConst ``FVar.here) h rest
  let inner ← fvarAt rest (j - 1)
  let .app (.app _ _) g := (← inferType inner)
    | throwError "verified_compile: the reference {inner}"
  return mkApp4 (mkConst ``FVar.there) rest g h inner

/-- The proof that `funs.get fv env` is `F env` for the meaning `F` of the function that `fv`
names, by `Funs.get_there` and `Funs.get_here`, for `funs` a chain of `Funs.cons`. -/
partial def getChain (funs fv env : Lean.Expr) : MetaM Lean.Expr := do
  let (``Funs.cons, #[S, h, F, rest]) := funs.getAppFnArgs
    | throwError "verified_compile: the meanings {funs}"
  match fv.getAppFnArgs with
  | (``FVar.here, _) => return mkAppN (mkConst ``Funs.get_here) #[S, h, F, rest, env]
  | (``FVar.there, #[_, g, _, v]) =>
    transHint (mkAppN (mkConst ``Funs.get_there) #[S, g, h, F, rest, v, env])
      (← getChain rest v env)
  | _ => throwError "verified_compile: the function reference {fv}"

def addDefinition (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addAndCompile <| .defnDecl <|
    mkDefinitionValEx name [] type value (.regular 1) .safe [name]

def addTheorem (name : Name) (type value : Lean.Expr) : CoreM Unit :=
  addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- Whether the kernel finds `a` and `b` definitionally equal, in the current local context. -/
def kernelDefEq (a b : Lean.Expr) : MetaM Bool := do
  match Kernel.isDefEq (← getEnv) (← getLCtx) a b with
  | .ok r => return r
  | .error ex => throwKernelException ex

/-- The proof of `T = e` by `rfl`, for a term `T` that the reflector reflects in place of `e`:
the two differ by a `let` that `T` substitutes, a beta reduction, or a match on a constructor,
which the kernel reduces without evaluating either term's parts. -/
def bareEq (T e : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl e) (← mkEq T e)

/-- The enumeration and its `Flat` instance, for a type other than `Bool` whose values are
enumeration constants with a `Flat` instance to words. -/
def enumFlat? (type : Lean.Expr) : MetaM (Option (Name × Lean.Expr)) := do
  if (← elemOf? type).isSome then return none
  let .const n _ ← whnfR type | return none
  unless ← isEnumType n do return none
  let some (β, inst) ← flatInstance? (mkConst n) | return none
  unless (← whnfR β).isConstOf ``UInt64 do return none
  return some (n, inst)

/-- `Flat.flat` of the enumeration `n` with the instance `inst`. -/
def enumFlat (n : Name) (inst : Lean.Expr) : Lean.Expr :=
  mkApp3 (mkConst ``LeanExe.Pipeline.Flat.flat) (mkConst n) (mkConst ``UInt64) inst

/-- The theorem that the flattening of the enumeration `n` is injective, added once per program
under `base`.  It follows from the decoder `fun w => bif w == flat K₁ then K₁ else …` and its
value at each constructor, which the kernel evaluates.  The reflector checks each constructor
first, so that a flattening that maps two constructors to one word is reported by name. -/
def flatInjective (base n : Name) (inst : Lean.Expr) : MetaM Lean.Expr := do
  let name := base ++ `flat_injective ++ n
  if (← getEnv).contains name then return mkConst name
  let .inductInfo info ← getConstInfo n | throwError "verified_compile: {n} is not an enumeration"
  let E := Lean.mkConst n
  let flat := enumFlat n inst
  let ctors := info.ctors.map Lean.mkConst
  let g ← withLocalDeclD `w (mkConst ``UInt64) fun w => do
    let rec chain : List Lean.Expr → MetaM Lean.Expr
      | [] => throwError "verified_compile: {n} has no constructors"
      | [k] => return k
      | k :: ks => do mkAppM ``cond #[← mkAppM ``BEq.beq #[w, mkApp flat k], k, ← chain ks]
    mkLambdaFVars #[w] (← chain ctors)
  let hgTy ← withLocalDeclD `x E fun x => do
    mkForallFVars #[x] (← mkEq (mkApp g (mkApp flat x)) x)
  let hg ← withLocalDeclD `x E fun x => do
    let motive ← withLocalDeclD `y E fun y => do
      mkLambdaFVars #[y] (← mkEq (mkApp g (mkApp flat y)) y)
    let minors ← ctors.mapM fun k => do
      let lhs := mkApp g (mkApp flat k)
      unless ← kernelDefEq lhs k do
        throwError "verified_compile: the flattening of {n} gives {k} the same word as an earlier \
          constructor"
      mkExpectedTypeHint (← mkEqRefl k) (← mkEq lhs k)
    mkLambdaFVars #[x] (mkAppN (mkConst (n ++ `casesOn) [Level.zero]) (#[motive, x] ++ minors))
  let hg ← mkExpectedTypeHint hg hgTy
  let proof ← withLocalDeclD `a E fun a => withLocalDeclD `b E fun b => do
    withLocalDeclD `h (← mkEq (mkApp flat a) (mkApp flat b)) fun h => do
      mkLambdaFVars #[a, b, h] (← mkEqTrans (← mkEqSymm (mkApp hg a))
        (← mkEqTrans (← mkCongrArg g h) (mkApp hg b)))
  addTheorem name (← mkAppM ``Function.Injective #[flat]) proof
  return mkConst name

/-- The word of an enumeration constant `e`, as a literal. -/
def enumWord? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let .const k _ := e | return none
  let some (.ctorInfo info) := (← getEnv).find? k | return none
  let some (n, inst) ← enumFlat? (mkConst info.induct) | return none
  let w ← match Kernel.whnf (← getEnv) (← getLCtx)
      (mkApp (mkConst ``UInt64.toNat) (mkApp (enumFlat n inst) e)) with
    | .ok w => pure w
    | .error ex => throwKernelException ex
  let some v := natOf w | throwError "verified_compile: the word of {e} is not a literal: {w}"
  return some (← mkAppOptM ``OfNat.ofNat #[some (mkConst ``UInt64), some (mkRawNatLit v), none])

/-- The components of a pair. -/
def pairFields (p : Lean.Expr) : MetaM (Array Lean.Expr) :=
  return #[← mkAppM ``Prod.fst #[p], ← mkAppM ``Prod.snd #[p]]

/-- For a match `app` with one discriminant `d` of a structure type, `Prod` included, and one
alternative `alt`, the proof of `alt (fields d) = app`.  It is proved by `cases` on a variable for
`d`, with a variable for the alternative, and then applied to both, so that the kernel evaluates
neither the value nor the alternative's body. -/
def casesEq (app : MatcherApp) (fields : Lean.Expr → MetaM (Array Lean.Expr)) :
    MetaM Lean.Expr := do
  let alt := app.alts[0]!
  let d := app.discrs[0]!
  let .lam _ _ motiveBody _ := app.motive
    | throwError "verified_compile: the match {app.toExpr} has an unexpected motive"
  if motiveBody.hasLooseBVars then
    throwError "verified_compile: the type of the match {app.toExpr} depends on its value"
  let altTy ← inferType alt
  let dTy ← inferType d
  let gen ← withLocalDeclD `h altTy fun h => withLocalDeclD `s dTy fun s => do
    let lhs := mkAppN h (← fields s)
    let rhs := { app with discrs := #[s], alts := #[h] }.toExpr
    let goal ← mkFreshExprMVar (← mkEq lhs rhs)
    for sg in ← goal.mvarId!.cases s.fvarId! do sg.mvarId.refl
    mkLambdaFVars #[h, s] (← instantiateMVars goal)
  return mkApp2 gen alt d

/-- From `proof : X = flatValue a` and `eq : a = e`, the proof of `X = flatValue e`. -/
def restate (proof eq : Lean.Expr) : MetaM Lean.Expr := do
  let some (_, _, e) := (← inferType eq).eq? | throwError "verified_compile: the equation {eq}"
  match (← shapeOf (← inferType e)).flat with
  | none => transHint proof eq
  | some f => transHint proof (← mkCongrArg f eq)

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
  if let some w ← enumWord? e then
    let src ← mkAppOptM ``Expr.word #[some c.sigs, some c.ctx, some w]
    return (src, ← rflProof c src (← flatValue e), .word)
  if !e.hasFVar && !e.hasLooseBVars && shape.flat.isNone then
    match shape.ty with
    | .word =>
      if (← wordLit? e).isSome then
        let src ← mkAppOptM ``Expr.word #[some c.sigs, some c.ctx, some e]
        return (src, ← rflProof c src e, .word)
    | .bool =>
      if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then
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
  if let .letE n type value body _ := e then
    if isPlace value then return ← reflectAs (body.instantiate1 value) e
    let s ← tyOf type
    if let .pair _ _ := s then
      let (src, proof, t) ← destructure c [] value fun a b => do
        return body.instantiate1 (← mkAppM ``Prod.mk #[a, b])
      -- The body at the pair of the value's components is the `let`, by eta for pairs.
      let lam := Lean.mkLambda n .default type body
      let eta ← mkAppM ``pair_eta #[lam, value]
      let some (_, lhs, _) := (← inferType eta).eq? | throwError "verified_compile: {eta}"
      return (src, ← restate proof (← mkExpectedTypeHint eta (← mkEq lhs e)), t)
    let (vs, hv, _) ← reflect c value
    -- The value's equation states the value itself, so that the body's equation substitutes it.
    let hv ← mkExpectedTypeHint hv (← mkEq (← denoteExpr c vs) (← flatValue value))
    let sv ← shapeOf type
    return ← withLocalDeclD `x type fun x => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (tyExpr s), some (sv.apply x), some c.env]
      let c' : Ctx := { c with vars := (x, s) :: c.vars, env := env' }
      let (bs, hb, t) ← reflect c' (body.instantiate1 x)
      let hb ← mkLambdaFVars #[x] hb
      let src ← mkAppM ``Expr.letE #[vs, bs]
      let proof ← if sv.flat.isNone then mkAppM ``letE_eq #[hv, hb]
        else mkAppM ``letE_flat_eq #[← sv.fn type, value, hv, hb]
      return (src, ← restate proof (← bareEq (body.instantiate1 value) e), t)
  if let some app ← matchMatcherApp? e then
    if app.discrs.size != 1 then
      throwError "verified_compile: a match on several values is not supported, in {e}"
    if app.discrInfos.any (·.hName?.isSome) then
      throwError "verified_compile: `match h : …` is not supported, in {e}"
    if let some (n, inst) ← enumFlat? (← inferType app.discrs[0]!) then
      return ← reflectEnumMatch app n inst
    if app.alts.size == 1 then
      let alt := app.alts[0]!
      let d := app.discrs[0]!
      if let (``Prod.mk, #[_, _, a, b]) := (projReduce d).getAppFnArgs then
        return ← reflectAs (alt.beta #[a, b]) e
      if let some (_, fields) ← structOf? (← inferType d) then
        -- The fields of a structure are its projections, of a variable bound to it first.
        let fieldsOf (y : Lean.Expr) : MetaM (Array Lean.Expr) := fields.mapM (mkProjection y)
        let (src, proof, t) ← if (projReduce d).isFVar then reflect c (alt.beta (← fieldsOf d))
          else reflect c (← withLetDecl `t (← inferType d) d fun y => do
            mkLetFVars #[y] (alt.beta (← fieldsOf y)))
        return (src, ← restate proof (← casesEq app fieldsOf), t)
      if let .elem _ ← tyOf (← inferType d) then
        -- The components of a tuple are its projections, of a variable bound to it first.
        let (src, proof, t) ← if (projReduce d).isFVar then reflect c (alt.beta (← pairFields d))
          else reflect c (← withLetDecl `t (← inferType d) d fun y => do
            mkLetFVars #[y] (alt.beta (← pairFields y)))
        return (src, ← restate proof (← casesEq app pairFields), t)
      let (src, proof, t) ← destructure c [] d fun a b => return alt.beta #[a, b]
      return (src, ← restate proof (← casesEq app pairFields), t)
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
  | ``Decidable.decide, #[p, inst] =>
    if let (``Ne, #[_, a, b]) := p.consumeMData.getAppFnArgs then
      -- `decide (a ≠ b)` is `!decide (a = b)`.
      let notEq ← mkAppOptM ``decide_not #[some (← mkEq a b), none, some inst]
      let T ← mkAppM ``not #[← mkDecide (← mkEq a b)]
      return ← reflectVia T (← mkExpectedTypeHint (← mkEqSymm notEq) (← mkEq T e))
    if let some r ← enumDecide? p inst then return r
    if let some (op, a, b) ← fcomparison? p then return ← reflectFCmp op a b
    let some (op, a, b) ← comparison? p
      | throwError "verified_compile: unsupported decision {p}"
    reflectCmp op a b
  | ``BEq.beq, #[α, inst, a, b] =>
    if let some r ← enumBEq? ``BEq.beq ``flat_beq α inst a b then return r
    if ← isFloat α then reflectFCmp .eq a b else reflectCmp .eq a b
  | ``bne, #[α, inst, a, b] =>
    if let some r ← enumBEq? ``bne ``flat_bne α inst a b then return r
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
      return ← reflectAs (← bindArgs e.getAppFn [α, inst, a, b] bind #[] #[]) e
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
  | ``LeanExe.Pipeline.Flat.flat, #[α, _, inst, a] =>
    let some (_, flatInst) ← enumFlat? α | throwError "verified_compile: unsupported term {e}"
    unless ← kernelDefEq inst flatInst do
      throwError "verified_compile: {e} uses a `Flat` instance other than {flatInst}"
    reflect c a
  | ``Prod.fst, #[_, _, p] =>
    if let .elem _ ← tyOf (← inferType p) then reflectProj e
    else destructure c [] p fun a _ => return a
  | ``Prod.snd, #[_, _, p] =>
    if let .elem _ ← tyOf (← inferType p) then reflectProj e
    else destructure c [] p fun _ b => return b
  | ``dite, #[α, p, inst, a, b] =>
    -- `if h : p then a else b` whose branches do not use `h` is `if p then a else b`.
    let .lam _ _ ta _ := a.consumeMData | throwError "verified_compile: unsupported term {e}"
    let .lam _ _ tb _ := b.consumeMData | throwError "verified_compile: unsupported term {e}"
    if ta.hasLooseBVars || tb.hasLooseBVars then
      throwError "verified_compile: the branches of {e} use the hypothesis of the `if`"
    reflectAs (← mkAppOptM ``ite #[some α, some p, some inst, some ta, some tb]) e
  | ``ite, #[α, p, inst, a, b] =>
    if let some r ← enumIte? α p inst a b then return r
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
    let cs ← mkAppOptM ``Expr.bool
      #[some c.sigs, some (ctxExpr (t :: c.vars.map (·.2))), some (mkConst ``Bool.true)]
    let sa ← shapeOf α
    let src ← mkAppM ``Expr.loop #[ns, is, cs, bs]
    let proof ← if sa.flat.isNone then mkAppM ``loop_eq #[hn, hi, hb]
      else mkAppM ``loop_flat_eq #[← sa.fn α, init, f, hn, hi, hb]
    return (src, ← mkExpectedTypeHint proof (← mkEq (← denoteExpr c src) (← flatValue e)), t)
  | ``LeanExe.repeatWhile, #[α, n, init, cnd, step] =>
    let (ns, hn, _) ← reflect c n
    let (is, hi, t) ← reflect c init
    let (cs, hc, _) ← reflectUnder1 c α t fun acc => return cnd.beta #[acc]
    let (bs, hb, _) ← reflectUnder c [] (mkConst ``UInt64) α .word t fun _ acc =>
      return step.beta #[acc]
    let sa ← shapeOf α
    let src ← mkAppM ``Expr.loop #[ns, is, cs, bs]
    let proof ← if sa.flat.isNone then mkAppM ``repeatWhile_eq #[hn, hi, cnd, step, hc, hb]
      else mkAppM ``repeatWhile_flat_eq #[← sa.fn α, init, cnd, step, hn, hi, hc, hb]
    return (src, ← mkExpectedTypeHint proof (← mkEq (← denoteExpr c src) (← flatValue e)), t)
  | ``Array.set!, setArgs@#[α, xs, k, v] =>
    let se ← shapeOf α
    let .elem el := se.ty | throwError "verified_compile: unsupported array {e}"
    let (``UInt64.toNat, #[i]) := k.consumeMData.getAppFnArgs
      | throwError "verified_compile: a position must be `i.toNat` for a word `i`, in {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (setArgs.set! 1 a))) e
    let (x, t) ← varOf c xs
    unless t == .array el do throwError "verified_compile: {xs} is not an array variable"
    let (is, hi, _) ← reflect c i
    let (vs, hv, _) ← reflect c v
    let src ← mkAppOptM ``Expr.set #[some c.sigs, some c.ctx, none, some x, some is, some vs]
    if se.flat.isNone then return (src, ← mkAppM ``set_eq #[x, hi, hv], .array el)
    return (src, ← mkAppM ``set_map_eq #[← se.fn α, x, xs, v, ← arrayEq x xs, hi, hv], .array el)
  | ``Array.push, pushArgs@#[α, xs, v] =>
    let se ← shapeOf α
    let .elem el := se.ty | throwError "verified_compile: unsupported array {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (pushArgs.set! 1 a))) e
    let (x, t) ← varOf c xs
    unless t == .array el do throwError "verified_compile: {xs} is not an array variable"
    let (vs, hv, _) ← reflect c v
    let src ← mkAppOptM ``Expr.push #[some c.sigs, some c.ctx, none, some x, some vs]
    if se.flat.isNone then return (src, ← mkAppM ``push_eq #[x, hv], .array el)
    return (src, ← mkAppM ``push_map_eq #[← se.fn α, x, xs, v, ← arrayEq x xs, hv], .array el)
  | ``HAppend.hAppend, appendArgs@#[α, _, _, _, xs, ys] =>
    let .array el ← tyOf α | throwError "verified_compile: unsupported term {e}"
    let xs := projReduce xs
    let ys := projReduce ys
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (appendArgs.set! 4 a))) e
    unless ys.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType ys) ys fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (appendArgs.set! 5 a))) e
    let (x, _) ← varOf c xs
    let (y, _) ← varOf c ys
    let src ← mkAppOptM ``Expr.append #[some c.sigs, some c.ctx, none, some x, some y]
    let (``Array, #[β]) := (← whnfR α).getAppFnArgs
      | throwError "verified_compile: unsupported term {e}"
    let se ← shapeOf β
    if se.flat.isNone then return (src, ← rflProof c src e, .array el)
    return (src, ← mkAppOptM ``append_map_eq #[some c.sigs, some c.ctx, some c.funs, some c.env,
      none, none, some (← se.fn β), some x, some y, some xs, some ys, some (← arrayEq x xs),
      some (← arrayEq y ys)], .array el)
  | ``LeanExe.build, #[α, n, f] =>
    let se ← shapeOf α
    let .elem el := se.ty | throwError "verified_compile: unsupported array {e}"
    let (ns, hn, _) ← reflect c n
    let (fs, hf) ← withLocalDeclD `i (mkConst ``UInt64) fun i => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (mkConst ``Ty.word), some i, some c.env]
      let c' : Ctx := { c with vars := (i, .word) :: c.vars, env := env' }
      let (fs, hf, t) ← reflect c' (f.beta #[i])
      unless t == .elem el do throwError "verified_compile: an element of {e} is not a {α}"
      return (fs, ← mkLambdaFVars #[i] hf)
    let src ← mkAppM ``Expr.build #[ns, fs]
    if se.flat.isNone then return (src, ← mkAppM ``build_eq #[hn, hf], .array el)
    return (src, ← mkAppM ``build_map_eq #[← se.fn α, f, hn, hf], .array el)
  | ``Nat.toUInt64, #[n] =>
    let (``Array.size, sizeArgs@#[_, xs]) := n.consumeMData.getAppFnArgs
      | throwError "verified_compile: unsupported term {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn #[mkAppN n.consumeMData.getAppFn (sizeArgs.set! 1 a)])) e
    let (x, t) ← varOf c xs
    let .array _ := t | throwError "verified_compile: {xs} is not an array variable"
    let src ← mkAppOptM ``Expr.size #[some c.sigs, some c.ctx, none, some x]
    let (``Array, #[β]) := (← whnfR (← inferType xs)).getAppFnArgs
      | throwError "verified_compile: {xs} is not an array"
    let se ← shapeOf β
    if se.flat.isNone then return (src, ← rflProof c src e, .word)
    return (src, ← mkAppOptM ``size_map_eq #[some c.sigs, some c.ctx, some c.funs, some c.env,
      none, none, some (← se.fn β), some x, some xs, some (← arrayEq x xs)], .word)
  | ``getElem!, getArgs@#[_, _, β, _, _, inh, xs, k] =>
    let (``UInt64.toNat, #[i]) := k.consumeMData.getAppFnArgs
      | throwError "verified_compile: an index must be `i.toNat` for a word `i`, in {e}"
    let xs := projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (getArgs.set! 6 a))) e
    let (x, t) ← varOf c xs
    let .array el := t | throwError "verified_compile: {xs} is not an array variable"
    let (is, hi, _) ← reflect c i
    let src ← mkAppOptM ``Expr.get #[some c.sigs, some c.ctx, none, some x, some is]
    let se ← shapeOf β
    if se.flat.isNone then return (src, ← mkAppM ``get_eq #[x, hi], .elem el)
    -- A read past the end gives the flattening of Lean's default element, which must be the
    -- element type's default.
    let lhs := se.apply (mkApp2 (mkConst ``Inhabited.default [Level.one]) β inh)
    let rhs := mkApp2 (mkConst ``Inhabited.default [Level.one])
      (mkApp (mkConst ``Elem.denote) (elemExpr el))
      (mkApp (mkConst ``Elem.instInhabited) (elemExpr el))
    unless ← kernelDefEq lhs rhs do
      throwError "verified_compile: the flattening of the default {β} is not the default element; \
        the default must take each field's default, and an enumeration's default must have the \
        word 0"
    let hd ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs)
    let proof ← mkAppOptM ``get_map_eq #[none, none, none, none, none, some β, some inh,
      some (← se.fn β), some hd, some x, some xs, none, none, some (← arrayEq x xs), some hi]
    return (src, proof, .elem el)
  | _, _ => throwError "verified_compile: unsupported term {e}"
where
  /-- The proof by `rfl` that the source value of the array variable `xs` is its flattening. -/
  arrayEq (x xs : Lean.Expr) : MetaM Lean.Expr := do
    let v ← flatValue xs
    mkExpectedTypeHint (← mkEqRefl v) (← mkEq (← mkAppM ``Env.get #[c.env, x]) v)
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
  /-- `e`, reflected as the term `T` with `eq : T = e`. -/
  reflectVia (T eq : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (src, proof, t) ← reflect c T
    return (src, ← restate proof eq, t)
  /-- The `LawfulBEq` instance of an enumeration, which `==` on it needs. -/
  enumLawful (α beq : Lean.Expr) : MetaM Lean.Expr := do
    let some inst ← synthInstance? (mkApp2 (mkConst ``LawfulBEq [Level.zero]) α beq)
      | throwError "verified_compile: `==` on {α} needs `LawfulBEq {α}`; derive `DecidableEq`, or \
          `BEq` and `LawfulBEq`"
    return inst
  /-- `==` or `!=` (the function `op`) on enumerations, as the same comparison of their words,
  by the lemma `thm`. -/
  enumBEq? (op thm : Name) (α inst a b : Lean.Expr) :
      MetaM (Option (Lean.Expr × Lean.Expr × Ty)) := do
    let some (n, flatInst) ← enumFlat? α | return none
    let h ← flatInjective c.base n flatInst
    let lawful ← enumLawful α inst
    let flat := enumFlat n flatInst
    let eq ← mkAppOptM thm #[some α, some flatInst, some inst, some lawful, some h, some a, some b]
    return some (← reflectVia (← mkAppM op #[mkApp flat a, mkApp flat b]) (← mkEqSymm eq))
  /-- `decide (a = b)` on enumerations, as the same decision on their words. -/
  enumDecide? (p inst : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Ty)) := do
    let (``Eq, #[_, a, b]) := p.consumeMData.getAppFnArgs | return none
    let some (n, flatInst) ← enumFlat? (← inferType a) | return none
    let h ← flatInjective c.base n flatInst
    let flat := enumFlat n flatInst
    let eq ← mkAppOptM ``flat_decide #[none, some flatInst, some h, some a, some b, some inst]
    let words ← mkEq (mkApp flat a) (mkApp flat b)
    return some (← reflectVia (← mkDecide words) (← mkEqSymm eq))
  /-- `e`, reflected as `T`, which equals it by `bareEq`. -/
  reflectAs (T e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let (src, proof, t) ← reflect c T
    return (src, ← restate proof (← bareEq T e), t)
  /-- `if a = b` and `if a ≠ b` on enumerations, as the same test on their words. -/
  enumIte? (α p inst x y : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr × Ty)) := do
    let (thm, rel, a, b) ← match p.consumeMData.getAppFnArgs with
      | (``Eq, #[_, a, b]) => pure (``flat_ite, ``Eq, a, b)
      | (``Ne, #[_, a, b]) => pure (``flat_ite_ne, ``Ne, a, b)
      | _ => return none
    let some (n, flatInst) ← enumFlat? (← inferType a) | return none
    let h ← flatInjective c.base n flatInst
    let flat := enumFlat n flatInst
    let eq ← mkAppOptM thm #[none, some α, some flatInst, some h, some a, some b, some inst,
      some x, some y]
    let test ← mkAppM rel #[mkApp flat a, mkApp flat b]
    return some (← reflectVia (← mkAppM ``ite #[test, x, y]) (← mkEqSymm eq))
  /-- A `match` on an enumeration value `d`: the chain of `if`s on its word that chooses each
  constructor's alternative, proved equal to the match by cases on a variable for `d`, with
  variables for the alternatives, so that the kernel evaluates only the tests.  A value that is
  not a variable is bound with `let` first. -/
  reflectEnumMatch (app : MatcherApp) (n : Name) (inst : Lean.Expr) :
      MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let d := app.discrs[0]!
    unless (projReduce d).isFVar do
      return ← reflectAs (← withLetDecl `t (← inferType d) d fun y => do
        mkLetFVars #[y] { app with discrs := #[y] }.toExpr) app.toExpr
    unless app.remaining.isEmpty do
      throwError "verified_compile: the match {app.toExpr} is applied to further arguments"
    let .lam _ _ resultTy _ := app.motive
      | throwError "verified_compile: the match {app.toExpr} has an unexpected motive"
    if resultTy.hasLooseBVars then
      throwError "verified_compile: the type of the match {app.toExpr} depends on its value"
    let .inductInfo info ← getConstInfo n | throwError "verified_compile: {n} is not an enumeration"
    let E := Lean.mkConst n
    let flat := enumFlat n inst
    let altTys ← app.alts.mapM inferType
    let hyps := (List.range app.alts.size).toArray.map fun i => (Name.mkSimple s!"h{i}", altTys[i]!)
    withLocalDeclsDND hyps fun hs => withLocalDeclD `x E fun x => do
      -- The alternative that each constructor reaches, with its arguments.
      let choices ← info.ctors.mapM fun k => do
        let r ← reduceMatcher? { app with discrs := #[mkConst k], alts := hs }.toExpr
        let .reduced v := r
          | throwError "verified_compile: cannot reduce the match {app.toExpr} at {k}"
        let some j := hs.findIdx? (· == v.getAppFn)
          | throwError "verified_compile: the match {app.toExpr} at {k} gives {v}"
        let args ← v.getAppArgs.mapM fun a => do
          if a.isConstOf ``Unit.unit then return a
          if a.isConstOf k then return x
          throwError "verified_compile: the match {app.toExpr} at {k} passes {a}"
        return (k, j, args)
      -- The alternatives in order, each with the constructors that reach it.  An alternative
      -- before the last is reached by one constructor: a constructor pattern names one, and a
      -- variable or a wildcard takes all the remaining ones, after which Lean admits no other.
      let groups := (List.range app.alts.size).filterMap fun j =>
        match choices.filter (·.2.1 == j) with
        | [] => none
        | cs@((_, _, args) :: _) => some (cs.map (·.1), j, args)
      let rec chain (alts : Array Lean.Expr) (beta : Bool) :
          List (List Name × Nat × Array Lean.Expr) → MetaM Lean.Expr
        | [] => throwError "verified_compile: the match {app.toExpr} has no alternatives"
        | [(_, j, args)] => return if beta then alts[j]!.beta args else mkAppN alts[j]! args
        | ([k], j, args) :: rest => do
          let test ← mkAppM ``BEq.beq #[mkApp flat x, mkApp flat (Lean.mkConst k)]
          let branch := if beta then alts[j]!.beta args else mkAppN alts[j]! args
          mkAppM ``ite #[← mkEq test (mkConst ``Bool.true), branch, ← chain alts beta rest]
        | (ks, _, _) :: _ =>
          throwError "verified_compile: the alternative of {ks} in {app.toExpr} is not the last"
      let chainAbs ← chain hs false groups
      let matchAbs := { app with discrs := #[x], alts := hs }.toExpr
      let motive ← mkLambdaFVars #[x] (← mkEq chainAbs matchAbs)
      let minors ← info.ctors.toArray.mapM fun k => do
        let lhs := chainAbs.replaceFVar x (mkConst k)
        let rhs := matchAbs.replaceFVar x (mkConst k)
        unless ← kernelDefEq lhs rhs do
          throwError "verified_compile: the tests on the words of {n} do not choose the \
            alternative of {k}; the flattening may map two constructors to one word"
        mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs rhs)
      let cases := mkAppN (mkConst (n ++ `casesOn) [Level.zero]) (#[motive, x] ++ minors)
      let gen ← mkLambdaFVars (hs.push x) cases
      let eq := mkAppN gen (app.alts.push d)
      -- The chain with the actual alternatives and value, reflected.
      let chainReal := (← chain app.alts true groups).replaceFVar x d
      reflectVia chainReal eq
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
  /-- The reflection of `body a` with `a : α` of type `s` as variable 0, with its proof abstracted
  over `a`, which is split when it has a pair type. -/
  reflectUnder1 (c : Ctx) (α : Lean.Expr) (s : Ty) (body : Lean.Expr → MetaM Lean.Expr) :
      MetaM (Lean.Expr × Lean.Expr × Ty) :=
    withLocalDeclD `a α fun a => do
      let env' ← mkAppOptM ``Env.cons
        #[some c.ctx, some (tyExpr s), some (← flatValue a), some c.env]
      let c' : Ctx := { c with vars := (a, s) :: c.vars, env := env' }
      let (bs, hb, u) ← reflectSplit c' [a] (← body a)
      return (bs, ← mkLambdaFVars #[a] hb, u)
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
  /-- A component of a tuple or a field of a structure, `e`, a chain of `Prod.fst`, `Prod.snd`,
  and structure projections: the projection of a variable along a path, with a value that is not
  a variable bound with `let` first.  Besides the base and the path, the walk returns the chain as
  a function of the base. -/
  reflectProj (e : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr × Ty) := do
    let rec walk (e : Lean.Expr) (steps : List Bool) :
        MetaM (Lean.Expr × List Bool × (Lean.Expr → MetaM Lean.Expr)) := do
      let e := projReduce e
      let down (p : Lean.Expr) (path : List Bool) (step : Lean.Expr → MetaM Lean.Expr) := do
        let (base, steps, chain) ← walk p (path ++ steps)
        return (base, steps, fun y => do step (← chain y))
      match e.getAppFnArgs with
      | (``Prod.fst, #[_, _, p]) =>
        if let .elem _ ← tyOf (← inferType p) then down p [false] (mkAppM ``Prod.fst #[·])
        else return (e, steps, pure)
      | (``Prod.snd, #[_, _, p]) =>
        if let .elem _ ← tyOf (← inferType p) then down p [true] (mkAppM ``Prod.snd #[·])
        else return (e, steps, pure)
      | _ =>
        let some (i, p) ← structProj? e | return (e, steps, pure)
        let some path ← fieldPath? (← inferType p) i | return (e, steps, pure)
        let some (_, fields) ← structOf? (← inferType p) | return (e, steps, pure)
        down p path (mkProjection · fields[i]!)
    let (base, steps, chain) ← walk e []
    if base.isFVar then
      let (x, t) ← varOf c base
      let .elem be := t | throwError "verified_compile: {base} is not a tuple"
      let (path, target) ← pathExpr be steps
      let src ← mkAppOptM ``Expr.proj #[some c.sigs, some c.ctx, some (elemExpr be),
        some (elemExpr target), some x, some path]
      return (src, ← rflProof c src (← flatValue e), .elem target)
    reflectAs (← withLetDecl `t (← inferType base) base fun y => do
      mkLetFVars #[y] (← chain y)) e
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
    unless args.size == callee.sig.params.length do
      throwError "verified_compile: {fn} must be applied to all {callee.sig.params.length} \
        arguments"
    let bind := (args.toList.zip callee.sig.params).zipIdx.map fun ((a, t), i) =>
      !t.scalar && if callee.sig.mode i = .owned then !(projReduce a).isFVar
        else !isPlace a
    if bind.any id then
      return some (← reflectAs (← bindArgs e.getAppFn args.toList bind #[] #[]) e)
    let reflected ← args.toList.mapM (reflect c)
    let nilArgs ← mkAppOptM ``Args.nil #[some c.sigs, some c.ctx]
    let argList ← reflected.foldrM (fun (s, _, _) acc => mkAppM ``Args.cons #[s, acc]) nilArgs
    let nilEq ← mkAppOptM ``ofFn_nil_eq #[some c.sigs, some c.ctx, some c.funs, some c.env]
    let hargs ← reflected.foldrM (fun (_, h, _) acc => mkAppM ``ofFn_cons_eq #[h, acc]) nilEq
    let values ← envExpr (args.toList.zip callee.sig.params)
    let f ← fvarAt c.sigs j
    -- `funs.get f values` is the callee's meaning by `getChain`, and the callee's equation gives
    -- its value, with no unfolding of the callee's definition.
    let hf ← transHint (← getChain c.funs f values)
      (mkAppN (mkConst callee.denoteEq) args)
    let src ← mkAppM ``Expr.call #[f, ← mkAppM ``Args.get #[argList]]
    return some (src, ← mkAppM ``call_eq #[f, hargs, hf], callee.sig.result)
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

/-- The instance that Lean synthesizes for `userT`, which the theorem's statement uses. -/
def userInst (userT : Lean.Expr) : MetaM Lean.Expr := do
  let some inst ← synthInstance? (mkApp (mkConst ``LeanExe.Pipeline.Represent) userT)
    | throwError "verified_compile: Lean has no `Represent` instance for {userT}, so no theorem \
        can be stated for it"
  return inst

/-- `proof` as a proof of `Agree inst src.2 φ`, for Lean's instance `inst` for `userT`; the kernel
checks that the two types are equal by unfolding. -/
def agreeAs (userT inst : Lean.Expr) (src : Lean.Expr × Lean.Expr) (φ proof : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  return (φ, ← mkExpectedTypeHint proof (mkAppN (mkConst ``Agree) #[userT, src.1, inst, src.2, φ]))

/-- The proof by `rfl` of `prop`, of the form `∀ xs, a = b`, after a check that `a` and `b` are
equal by unfolding. -/
def eqByUnfolding (prop userT : Lean.Expr) : MetaM Lean.Expr :=
  forallTelescope prop fun xs eq => do
    let some (_, a, b) := eq.eq? | throwError "verified_compile: {eq} is not an equation"
    unless ← withTransparency .all (isDefEq a b) do
      throwError "verified_compile: the words of {userT} and of its flattening differ: {a} and {b}"
    mkLambdaFVars xs (← mkExpectedTypeHint (← mkEqRefl a) eq)

/-- The proof of `b = true` by evaluation, which the kernel checks. -/
def trueByEval (b : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
    (← mkEq b (mkConst ``Bool.true))

/-- The flattening of `userT` as a lambda, the identity when nothing in it is flattened.  The
theorem applies it to Lean's values, so it carries no type annotation that would keep the
application from reducing by beta reduction. -/
def flatFn (userT : Lean.Expr) : MetaM Lean.Expr := do
  if let some f := (← shapeOf userT).flat then return f
  withLocalDeclD `x userT fun x => mkLambdaFVars #[x] x

/-- `Agree.refl` for a type that the reflector does not flatten, after a check that Lean's instance
unfolds to the source instance. -/
def agreeRefl (userT inst : Lean.Expr) (src : Lean.Expr × Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  unless ← withTransparency .all (isDefEq inst src.2) do
    throwError "verified_compile: Lean's instance for {userT} does not unfold to the source \
      instance"
  agreeAs userT inst src (← withLocalDeclD `x userT fun x => mkLambdaFVars #[x] x)
    (← mkAppM ``Agree.refl #[inst])

/-- `Agree.scalar` for a type without arrays, whose source instance comes from `srcScalar`, along
the flattening `φ`. -/
def agreeScalar (userT inst : Lean.Expr) (src : Lean.Expr × Lean.Expr) (srcScalar φ : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let some userScalar ← synthInstance? (mkApp (mkConst ``LeanExe.Pipeline.Scalar) userT)
    | throwError "verified_compile: Lean has no `Scalar` instance for {userT}"
  let app ← mkAppOptM ``Agree.scalar #[some userT, some src.1, some userScalar, some srcScalar,
    some φ]
  let .forallE _ hTy _ _ ← inferType app | throwError "verified_compile: `Agree.scalar`"
  agreeAs userT inst src φ (mkApp app (← eqByUnfolding hTy userT))

/-- The flattening of an array of the structure type `el`, inside `Moved` for `Agree.flatMoved`,
and the proof of agreement by `thm`, `Agree.flatArray` or `Agree.flatMoved`. -/
def agreeArray (thm : Name) (el : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let se ← shapeOf el
  let .elem e := se.ty | throwError "verified_compile: an array holds elements, not {el}"
  let app ← mkAppOptM thm #[some el, none, none, none, some (elemExpr e), some (← se.fn el)]
  let .forallE _ hφTy concl _ ← inferType app
    | throwError "verified_compile: the hypothesis of {thm}"
  return (concl.appArg!, mkApp app (← eqByUnfolding hφTy el))

/-- The flattening of pairs from the flattenings of their components and the agreement by
`Agree.prod` from the components' agreements. -/
def agreeProd (a b : Lean.Expr × Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let proof ← mkAppM ``Agree.prod #[a.2, b.2]
  return (← Core.betaReduce (← inferType proof).appArg!, proof)

/-- The flattening of Lean's values of type `userT` to the meaning of `t`, and the proof that the
instance Lean synthesizes for `userT` agrees with `Ty.leanInst t` along it: `Agree.scalar` for a
type without arrays, `Agree.flatArray` for an array of structures, `Agree.refl` for another array,
and `Agree.prod` for a pair that holds arrays. -/
partial def agreeTy (userT : Lean.Expr) (t : Ty) : MetaM (Lean.Expr × Lean.Expr) := do
  let inst ← userInst userT
  let src := (mkApp (mkConst ``Ty.denote) (tyExpr t), mkApp (mkConst ``Ty.leanInst) (tyExpr t))
  -- Every agreement is stated along `flatFn userT`, the flattening of the equation's right side.
  let φ ← flatFn userT
  if t.scalar then
    let h ← trueByEval (mkApp (mkConst ``Ty.scalar) (tyExpr t))
    return ← agreeScalar userT inst src (mkApp2 (mkConst ``Ty.scalarInst) (tyExpr t) h) φ
  match t, (← whnfR userT).getAppFnArgs with
  | .array _, (``Array, #[el]) =>
    if (← shapeOf el).flat.isNone then return ← agreeRefl userT inst src
    let (_, proof) ← agreeArray ``Agree.flatArray el
    agreeAs userT inst src φ proof
  | .pair a b, (``Prod, #[ua, ub]) =>
    let (_, proof) ← agreeProd (← agreeTy ua a) (← agreeTy ub b)
    agreeAs userT inst src φ proof
  | _, _ => throwError "verified_compile: the type {userT} does not have the shape of {tyExpr t}"

/-- The flattening of an argument of type `userT`, a value of `t.argTy m`, and the proof of
agreement with `t.argInst m`. -/
def agreeArg (userT : Lean.Expr) (t : Ty) (m : Mode) : MetaM (Lean.Expr × Lean.Expr) := do
  let inst ← userInst userT
  let src := (mkApp2 (mkConst ``Ty.argTy) (tyExpr t) (modeExpr m),
    mkApp2 (mkConst ``Ty.argInst) (tyExpr t) (modeExpr m))
  match t, m, (← whnfR userT).getAppFnArgs with
  | .array _, .owned, (``LeanExe.Pipeline.Moved, #[a]) =>
    let (``Array, #[el]) := (← whnfR a).getAppFnArgs
      | throwError "verified_compile: {a} is not an array"
    if (← shapeOf el).flat.isNone then return ← agreeRefl userT inst src
    let (φ, proof) ← agreeArray ``Agree.flatMoved el
    agreeAs userT inst src φ proof
  | _, _, _ =>
    let (φ, proof) ← agreeTy userT t
    agreeAs userT inst src φ proof

/-- The flattening of the tuple of a definition's arguments, of type `userT`, a value of
`argsTy ps ms`, and the proof of agreement with `argsInst ps ms`, by the cases of `argsInst`. -/
partial def agreeArgs (userT : Lean.Expr) (ps : List Ty) (ms : List Mode) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let inst ← userInst userT
  let src := (mkApp2 (mkConst ``argsTy) (ctxExpr ps) (modesExpr ms),
    mkApp2 (mkConst ``argsInst) (ctxExpr ps) (modesExpr ms))
  if ps.all Ty.scalar then
    let h ← trueByEval (← mkAppM ``List.all #[ctxExpr ps, mkConst ``Ty.scalar])
    let φ ← if ps.isEmpty then withLocalDeclD `x userT fun x => mkLambdaFVars #[x] x
      else flatFn userT
    return ← agreeScalar userT inst src
      (mkApp3 (mkConst ``argsScalarInst) (ctxExpr ps) (modesExpr ms) h) φ
  match ps, (← whnfR userT).getAppFnArgs with
  | [t], _ =>
    let (φ, proof) ← agreeArg userT t (ms.headD .borrowed)
    agreeAs userT inst src φ proof
  | t :: u :: ts, (``Prod, #[ua, ub]) =>
    let (φ, proof) ← agreeProd (← agreeArg ua t (ms.headD .borrowed))
      (← agreeArgs ub (u :: ts) ms.tail)
    agreeAs userT inst src φ proof
  | _, _ => throwError "verified_compile: the arguments {userT} do not have the shape of the \
    parameters"

/-- What the reflector learns from one definition: its signature, whether a call may trap, the
modes of its parameters, and whether its code takes the call depth. -/
structure Reflected where
  name : Name
  params : List Ty
  result : Ty
  aborts : Bool
  modes : List Mode
  depth : Bool
  /-- The equation `∀ args, F (env of args) = flat (name args)` of the meaning `F` of the
  definition's function in the program's meanings. -/
  meaningEq : Name
  /-- The Lean type of the tuple of the definition's arguments, with `Moved` for an owned array. -/
  argsType : Lean.Expr
  /-- The Lean type of the definition's result. -/
  resultType : Lean.Expr
  /-- The flattening of the argument tuple, a lambda. -/
  flatArgs : Lean.Expr
  /-- The flattening of the result, a lambda. -/
  flatResult : Lean.Expr
  deriving Inhabited

/-- The weak head normal form of `e` by the kernel.  The reflector evaluates the compiler's
functions of a source body this way: Meta's `reduce` would recurse once per level of the body and
exceed the elaborator's recursion limit on a deep one. -/
def kernelWhnf (e : Lean.Expr) : MetaM Lean.Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => return r
  | .error ex => throwKernelException ex

/-- The modes of the list of modes `e`, evaluated by the kernel. -/
partial def modesOf (e : Lean.Expr) : MetaM (Option (List Mode)) := do
  match (← kernelWhnf e).getAppFnArgs with
  | (``List.nil, _) => return some []
  | (``List.cons, #[_, m, rest]) =>
    let m ← kernelWhnf m
    let m? := if m.isConstOf ``Mode.owned then some Mode.owned
      else if m.isConstOf ``Mode.borrowed then some Mode.borrowed else none
    match m?, ← modesOf rest with
    | some m, some ms => return some (m :: ms)
    | _, _ => return none
  | _ => return none

/-- The value of a Boolean property of a definition, which the kernel evaluates. -/
def boolOf (what : MessageData) (e : Lean.Expr) : MetaM Bool := do
  let v ← kernelWhnf e
  if v.isConstOf ``Bool.true then return true
  if v.isConstOf ``Bool.false then return false
  throwError "verified_compile: cannot evaluate {what}"

/-- The parameter modes that `Expr.paramChoice` gives for the source body `src` of `name`. -/
def paramChoiceOf (name : Name) (src : Lean.Expr) : MetaM (List Mode) := do
  let some modes ← modesOf (← mkAppM ``Expr.paramChoice #[src])
    | throwError "verified_compile: cannot evaluate the parameter modes of {name}"
  return modes

/-- The right-nested product of `tys`, `Unit` for none. -/
def tupleType : List Lean.Expr → MetaM Lean.Expr
  | [] => return mkConst ``Unit
  | [t] => return t
  | t :: ts => do mkAppM ``Prod #[t, ← tupleType ts]

/-- What `reflectDefinition` and `reflectRecursive` record of definition `name` with parameters
`params` of types `types` and result type `resultType`: Lean's tuple of the arguments, in which an
owned array has type `Moved`, the flattenings of the arguments and of the result, and the theorems
`base.argsAgree` and `base.resultAgree` that Lean's instances agree with the source instances
along them. -/
def finishReflected (base name : Name) (params : Array Lean.Expr) (types : List Ty) (result : Ty)
    (resultType : Lean.Expr) (aborts : Bool) (modes : List Mode) (depth : Bool)
    (meaningEq : Name) : MetaM Reflected := do
  let argTys ← (params.toList.zip (paramModes types modes)).mapM fun (p, m) => do
    let ty ← inferType p
    return if m == .owned then mkApp (mkConst ``LeanExe.Pipeline.Moved) ty else ty
  let argsType ← tupleType argTys
  let (flatArgs, argsAgree) ← agreeArgs argsType types modes
  let (flatResult, resultAgree) ← agreeTy resultType result
  addTheorem (base ++ `argsAgree) (← inferType argsAgree) argsAgree
  addTheorem (base ++ `resultAgree) (← inferType resultAgree) resultAgree
  return ⟨name, types, result, aborts, modes, depth, meaningEq, argsType, resultType, flatArgs,
    flatResult⟩

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
    let (src, proof, _) ← reflect.reflectSplit ⟨base.getPrefix, sigs, funs, callees, vars, env⟩
      params.toList body
    let modes ← paramChoiceOf name src
    let funcType := mkApp (mkConst ``Func) sigs
    let func ← mkAppOptM ``Func.mk #[some sigs, some (toExpr name.getString!),
      some (ctxExpr types), some (tyExpr result), some src, some (← mkEqRefl (toExpr true)),
      some (modesExpr modes)]
    addDefinition (base ++ `func) funcType func
    let lhs ← mkAppM ``Func.denote #[mkConst (base ++ `func), funs, env]
    let eqType ← mkForallFVars params
      (← mkEq lhs (resultShape.apply (mkAppN (mkConst name) params)))
    -- `name = fun params => body` by `rfl`: against a lambda the kernel can only unfold `name`.
    -- Applied to the parameters, it relates the body to `name params` by beta reduction, so the
    -- kernel never compares `name params` with a body headed by a matcher, which it would unfold
    -- first, evaluating the matcher's discriminant.
    let value ← instantiateMVars info.value
    let hdef ← mkExpectedTypeHint (← mkEqRefl (mkConst name)) (← mkEq (mkConst name) value)
    let happ ← params.foldlM (fun h p => mkCongrFun h p) hdef
    let full ← restate proof (← mkEqSymm happ)
    addTheorem (base ++ `denote_eq) eqType (← mkLambdaFVars params full)
    let aborts ← boolOf m!"whether {name} may trap"
      (← mkAppM ``Func.aborts #[mkConst (base ++ `func)])
    let depth ← boolOf m!"whether the code of {name} takes the call depth"
      (← mkAppM ``Func.depth #[mkConst (base ++ `func)])
    finishReflected base name params types result (← inferType body) aborts modes depth
      (base ++ `denote_eq)

/-- The inverse `u` of the flattening `φ` of a Lean type, which the meaning of a recursive
definition applies to the values of its parameters, with the proofs of the two inverse laws at
given terms: `left a : u (φ a) = a` and `right v : φ (u v) = v`. -/
structure Inverse where
  u : Lean.Expr
  left : Lean.Expr → MetaM Lean.Expr
  right : Lean.Expr → MetaM Lean.Expr

/-- The proof of `x = y` by `rfl`, for terms that the kernel identifies by unfolding a flattening
and its inverse, by projections of constructors, and by structure eta, none of which evaluates a
definition. -/
def rflEq (x y : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl y) (← mkEq x y)

/-- The component of the tuple `x` along `steps`: `false` for a pair's first component and `true`
for its second. -/
def tuplePath (x : Lean.Expr) : List Bool → MetaM Lean.Expr
  | [] => return x
  | false :: rest => do tuplePath (← mkAppM ``Prod.fst #[x]) rest
  | true :: rest => do tuplePath (← mkAppM ``Prod.snd #[x]) rest

/-- The inverse of the flattening of a Lean type, `none` for a type that flattening leaves as it
is.  A pair maps its components, an array maps its elements, and a structure whose `Flat` instance
is a tuple of all its fields builds the structure from the tuple's components.  The laws hold by
`rfl`, except for an array, whose laws follow from its elements' by `map_inverse`.  An
enumeration has no inverse on the words that encode no constructor, and the reflector rejects it.
-/
partial def inverseOf? (type : Lean.Expr) : MetaM (Option Inverse) := do
  let sh ← shapeOf type
  let some φ := sh.flat | return none
  let type ← whnfR type
  let src := mkApp (mkConst ``Ty.denote) (tyExpr sh.ty)
  let inverse (u : Lean.Expr) (left right : Lean.Expr → MetaM Lean.Expr) : Inverse :=
    ⟨u, left, right⟩
  if let (``Prod, #[a, b]) := type.getAppFnArgs then
    let ia ← inverseOf? a
    let ib ← inverseOf? b
    let part (i : Option Inverse) (x : Lean.Expr) : Lean.Expr := match i with
      | some i => i.u.beta #[x]
      | none => x
    let u ← withLocalDeclD `v src fun v => do
      mkLambdaFVars #[v] (← mkAppOptM ``Prod.mk #[some a, some b,
        some (part ia (← mkAppM ``Prod.fst #[v])), some (part ib (← mkAppM ``Prod.snd #[v]))])
    let lawOf (i : Option Inverse) (f : Inverse → Lean.Expr → MetaM Lean.Expr) (x : Lean.Expr) :
        MetaM Lean.Expr := match i with
      | some i => f i x
      | none => mkEqRefl x
    let left (x : Lean.Expr) : MetaM Lean.Expr := do
      let h1 ← lawOf ia Inverse.left (← mkAppM ``Prod.fst #[x])
      let h2 ← lawOf ib Inverse.left (← mkAppM ``Prod.snd #[x])
      let h ← mkCongr (← mkCongrArg (mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) a b) h1)
        h2
      mkExpectedTypeHint h (← mkEq (u.beta #[φ.beta #[x]]) x)
    let right (v : Lean.Expr) : MetaM Lean.Expr := do
      let h1 ← lawOf ia Inverse.right (← mkAppM ``Prod.fst #[v])
      let h2 ← lawOf ib Inverse.right (← mkAppM ``Prod.snd #[v])
      let (α', β') ← match (← whnf (← inferType v)).getAppFnArgs with
        | (``Prod, #[α', β']) => pure (α', β')
        | _ => throwError "verified_compile: the flattening of {type} is not a pair"
      let h ← mkCongr
        (← mkCongrArg (mkApp2 (mkConst ``Prod.mk [Level.zero, Level.zero]) α' β') h1) h2
      mkExpectedTypeHint h (← mkEq (φ.beta #[u.beta #[v]]) v)
    return some (inverse u left right)
  if let (``Array, #[el]) := type.getAppFnArgs then
    let some ie ← inverseOf? el | return none
    let se ← shapeOf el
    let φe ← se.fn el
    let srcEl := mkApp (mkConst ``Ty.denote) (tyExpr se.ty)
    let u ← withLocalDeclD `v src fun v => do
      mkLambdaFVars #[v] (← mkAppOptM ``Array.map #[some srcEl, some el, some ie.u, some v])
    let left (x : Lean.Expr) : MetaM Lean.Expr := do
      let h ← withLocalDeclD `y el fun y => do mkLambdaFVars #[y] (← ie.left y)
      let p ← mkAppM ``map_inverse #[φe, ie.u, h, x]
      mkExpectedTypeHint p (← mkEq (u.beta #[φ.beta #[x]]) x)
    let right (v : Lean.Expr) : MetaM Lean.Expr := do
      let h ← withLocalDeclD `w srcEl fun w => do mkLambdaFVars #[w] (← ie.right w)
      let p ← mkAppM ``map_inverse #[ie.u, φe, h, v]
      mkExpectedTypeHint p (← mkEq (φ.beta #[u.beta #[v]]) v)
    return some (inverse u left right)
  let some (ctor, _) ← structOf? type
    | throwError "verified_compile: the parameter type {type} of a recursive definition holds an \
        enumeration, whose flattening has no inverse on the words that encode no constructor"
  let some (β, inst) ← flatInstance? type
    | throwError "verified_compile: the structure {type} has no `Flat` instance"
  let tree ← flatTree type β inst ctor
  unless tree.length == ctor.numFields do
    throwError "verified_compile: the `Flat` instance of {type} does not hold all its fields"
  let iβ ← inverseOf? β
  let u ← withLocalDeclD `v src fun v => do
    let w := match iβ with
      | some i => i.u.beta #[v]
      | none => v
    let fields ← (List.range ctor.numFields).mapM fun i => do
      let some (_, steps) := tree.find? (·.1 == i)
        | throwError "verified_compile: field {i} of {type} is missing from its `Flat` instance"
      tuplePath w steps
    let app := mkAppN (mkConst ctor.name type.getAppFn.constLevels!)
      (type.getAppArgs ++ fields.toArray)
    mkLambdaFVars #[v] app
  return some (inverse u (fun x => rflEq (u.beta #[φ.beta #[x]]) x)
    (fun v => rflEq (φ.beta #[u.beta #[v]]) v))

/-- The proof of `∀ env, P env` for environments of the context `ts`, from the proof that `k`
gives of `P (Env.cons v₀ (… Env.nil))` for variables `v₀ …` of the context's types. -/
partial def splitEnv (ts : List Ty) (P : Lean.Expr) (k : List Lean.Expr → MetaM Lean.Expr) :
    MetaM Lean.Expr := do
  match ts with
  | [] => return mkApp2 (mkConst ``env_forall_nil) P (← k [])
  | t :: rest =>
    let h ← withLocalDeclD `v (mkApp (mkConst ``Ty.denote) (tyExpr t)) fun v => do
      let P' ← withLocalDeclD `e (mkApp (mkConst ``Env) (ctxExpr rest)) fun e => do
        let cons ← mkAppOptM ``Env.cons #[some (ctxExpr rest), some (tyExpr t), some v, some e]
        mkLambdaFVars #[e] (mkApp P cons).headBeta
      mkLambdaFVars #[v] (← splitEnv rest P' fun vs => k (v :: vs))
    return mkAppN (mkConst ``env_forall_cons) #[tyExpr t, ctxExpr rest, P, h]

/-- `Env.cons v₀ (… Env.nil)` for values `vs` of the context `ts`. -/
def envOfValues : List Ty → List Lean.Expr → MetaM Lean.Expr
  | t :: ts, v :: vs => do
    mkAppOptM ``Env.cons #[some (ctxExpr ts), some (tyExpr t), some v, some (← envOfValues ts vs)]
  | _, _ => return mkConst ``Env.nil

/-- Reflects the recursive definition `name`, whose unfolding equation is `eqName`, as a
recursive function that may call itself and the functions `sigs`, meaning `funs`, after the
program `rest` with the proof `hRest` that `funs` are its meanings.  It adds `base.meaning`, the
function of an environment that the definition means; `base.meaning_eq`, its value at the
flattenings of arguments; `base.func`; `base.denote_eq`, the body's value; and `base.fixed`, the
equation that makes `base.meaning` the function's meaning in `Prog.Meaning`.  The equations never
make the kernel compare the definition at two different arguments, since its value is a
`WellFounded.fix`.  The parameter modes are the choice of `Expr.paramChoice` for the body
reflected with the modes before, from all borrowed, until the choice repeats or every parameter
has had a round. -/
def reflectRecursive (base name eqName : Name) (sigs funs rest hRest : Lean.Expr)
    (callees : List Callee) : MetaM Reflected := do
  let info ← getConstInfoDefn name
  unless info.levelParams.isEmpty do
    throwError "verified_compile: {name} has universe parameters"
  if (← collectAxioms name).contains ``sorryAx then
    throwError "verified_compile: the definition of {name} uses `sorry`"
  forallTelescope (← inferType (mkConst eqName)) fun params eqn => do
    let some (_, _, rhs) := eqn.eq?
      | throwError "verified_compile: the unfolding equation of {name} is {eqn}"
    let types ← params.toList.mapM fun p => do tyOf (← inferType p)
    let resultType ← inferType rhs
    let resultShape ← shapeOf resultType
    let result := resultShape.ty
    let ctx := ctxExpr types
    let vars := params.toList.zip types
    let env ← envExpr vars
    let invs ← params.toList.mapM fun p => do inverseOf? (← inferType p)
    -- The arguments at an environment `e`: the inverses of its values.
    let getAt (e : Lean.Expr) (i : Nat) : MetaM Lean.Expr := do
      let t := types[i]!
      let x ← mkAppOptM ``Var.ofIndex #[some (tyExpr t), some ctx, some (toExpr i),
        some (← mkEqRefl (mkApp (mkApp (mkConst ``Option.some [Level.zero]) (mkConst ``Ty))
          (tyExpr t)))]
      mkAppOptM ``Env.get #[some ctx, some (tyExpr t), some e, some x]
    let argsAt (e : Lean.Expr) : MetaM (List Lean.Expr) :=
      (List.range types.length).mapM fun i => do
        let g ← getAt e i
        return match invs[i]! with
          | some inv => inv.u.beta #[g]
          | none => g
    let meaningAt (e : Lean.Expr) : MetaM Lean.Expr := do
      return resultShape.apply (mkAppN (mkConst name) (← argsAt e).toArray)
    let envType := mkApp (mkConst ``Env) ctx
    let mValue ← withLocalDeclD `env envType fun e => do mkLambdaFVars #[e] (← meaningAt e)
    addDefinition (base ++ `meaning) (← mkArrow envType (mkApp (mkConst ``Ty.denote)
      (tyExpr result))) mValue
    let M := Lean.mkConst (base ++ `meaning)
    -- `M` at the flattenings of `params`: by unfolding `M`, then by the left inverse law at each
    -- argument, under the definition.
    let mid ← meaningAt env
    let step1 ← rflEq (mkApp M env) mid
    let argsEnv ← argsAt env
    let mut nameEq ← mkEqRefl (mkConst name)
    for i in [0:types.length] do
      let p := params[i]!
      let h ← match invs[i]! with
        | some inv => do mkExpectedTypeHint (← inv.left p) (← mkEq argsEnv[i]! p)
        | none => rflEq argsEnv[i]! p
      nameEq ← mkCongr nameEq h
    let step2 ← match resultShape.flat with
      | none => pure nameEq
      | some _ => mkCongrArg (← resultShape.fn resultType) nameEq
    let selfEq ← transHint step1 step2
    addTheorem (base ++ `meaning_eq)
      (← mkForallFVars params (← mkEq (mkApp M env)
        (resultShape.apply (mkAppN (mkConst name) params))))
      (← mkLambdaFVars params selfEq)
    -- The body, reflected with a callee for the definition itself as function 0.
    let selfSig (modes : List Mode) : Sig := ⟨types, result, true, modes, true⟩
    let reflectWith (modes : List Mode) : MetaM (Lean.Expr × Lean.Expr) := do
      let g := sigExpr (selfSig modes)
      let sigs' := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Sig) g sigs
      let funs' := mkAppN (mkConst ``Funs.cons) #[sigs, g, M, funs]
      let callees' := ⟨name, selfSig modes, base ++ `meaning_eq⟩ :: callees
      let (src, proof, _) ← reflect.reflectSplit
        ⟨base.getPrefix, sigs', funs', callees', vars, env⟩ params.toList rhs
      return (src, proof)
    let mut modes : List Mode := types.map fun _ => .borrowed
    let first ← reflectWith modes
    let mut src := first.1
    let mut proof := first.2
    for _ in [0:types.length] do
      let choice ← paramChoiceOf name src
      if choice == modes then break
      modes := choice
      let next ← reflectWith modes
      src := next.1
      proof := next.2
    let g := sigExpr (selfSig modes)
    let sigs' := mkApp3 (mkConst ``List.cons [Level.zero]) (mkConst ``Sig) g sigs
    let funs' := mkAppN (mkConst ``Funs.cons) #[sigs, g, M, funs]
    let func ← mkAppOptM ``RecFunc.mk #[some sigs, some (toExpr name.getString!), some ctx,
      some (tyExpr result), some (modesExpr modes), some src, some (← mkEqRefl (toExpr true))]
    addDefinition (base ++ `func) (mkApp (mkConst ``RecFunc) sigs) func
    let f := Lean.mkConst (base ++ `func)
    let body := mkApp2 (mkConst ``RecFunc.body) sigs f
    let denote (e : Lean.Expr) : Lean.Expr :=
      mkAppN (mkConst ``Expr.denote) #[sigs', funs', ctx, tyExpr result, body, e]
    let full ← restate proof (← mkEqSymm (mkAppN (mkConst eqName) params))
    addTheorem (base ++ `denote_eq)
      (← mkForallFVars params (← mkEq (denote env)
        (resultShape.apply (mkAppN (mkConst name) params))))
      (← mkLambdaFVars params full)
    -- The fixed-point equation at each environment `E`: `M E` unfolds to the definition at the
    -- inverses of `E`'s values, which is the body's value at their flattenings, which are `E`'s
    -- values by the right inverse law.
    let consRecApp := mkAppN (mkConst ``Prog.Meaning.consRec) #[sigs, f, rest, funs, M, hRest]
    let .forallE _ fixedType _ _ ← whnf (← inferType consRecApp)
      | throwError "verified_compile: the type of Prog.Meaning.consRec"
    let .forallE n envTy P0 bi := fixedType
      | throwError "verified_compile: the fixed-point equation {fixedType}"
    let P := Lean.mkLambda n bi envTy P0
    let fixed ← splitEnv types P fun vs => do
      let E ← envOfValues types vs
      let as ← argsAt E
      let step1 ← rflEq (mkApp M E) (← meaningAt E)
      let bodyEq := mkAppN (mkConst (base ++ `denote_eq)) as.toArray
      -- The flattenings of the arguments are the values `vs`.
      let mut envEq ← mkEqRefl (mkConst ``Env.nil)
      let mut flatTail := Lean.mkConst ``Env.nil
      for i in (List.range types.length).reverse do
        let t := types[i]!
        let rest := ctxExpr (types.drop (i + 1))
        let a := as[i]!
        let flat := (← shapeOf (← inferType params[i]!)).apply a
        let h ← match invs[i]! with
          | some inv => do mkExpectedTypeHint (← inv.right vs[i]!) (← mkEq flat vs[i]!)
          | none => rflEq flat vs[i]!
        let cons := mkApp2 (mkConst ``Env.cons) rest (tyExpr t)
        envEq ← mkCongr (← mkCongrArg cons h) envEq
        flatTail := mkApp2 cons flat flatTail
      let envEq' ← mkExpectedTypeHint envEq (← mkEq flatTail E)
      let denEq ← mkCongrArg (mkAppN (mkConst ``Expr.denote) #[sigs', funs', ctx, tyExpr result,
        body]) envEq'
      let h ← transHint (← transHint step1 (← mkEqSymm bodyEq)) denEq
      mkExpectedTypeHint h (mkApp P E).headBeta
    addTheorem (base ++ `fixed) fixedType fixed
    finishReflected base name params types result resultType true modes true
      (base ++ `meaning_eq)

/-- The values of the components of `x`, the tuple of a definition's arguments, as terms. -/
def argProjsE (x : Lean.Expr) : List Mode → Nat → MetaM (List Lean.Expr)
  | _, 0 => return []
  | ms, 1 => return [← argValE x (ms.headD .borrowed)]
  | ms, n + 2 => do
    return (← argValE (← mkAppM ``Prod.fst #[x]) (ms.headD .borrowed)) ::
      (← argProjsE (← mkAppM ``Prod.snd #[x]) ms.tail (n + 1))
where
  argValE (x : Lean.Expr) : Mode → MetaM Lean.Expr
    | .owned => mkAppM ``LeanExe.Pipeline.Moved.val #[x]
    | .borrowed => return x

/-- The proof of the theorem `claim` that the module computes the definition of `r`: the
compiler's theorem `h` for its source function, carried to Lean's instances by
`ImplementsA.transferAgree`.  The constant `funs` of the functions' meanings has the value
`funsVal`, a chain of `Funs.cons`.  The definition's equation `r.meaningEq` enters through
`Funs.get_there` and `Funs.get_here`, which take `funs.get` to the meaning of the definition's
function, and through plain lambdas for the flattenings, so that the kernel checks each step by
matching terms and by beta reduction and never unfolds the definition or its loops. -/
def implementsProof (funs : Name) (funsVal h F : Lean.Expr) (r : Reflected)
    (argsAgree resultAgree : Name) : MetaM Lean.Expr := do
  let hTy ← inferType h
  let #[α, γ, ia, ic, aborts, m, entry, f, _, _] := hTy.getAppArgs
    | throwError "verified_compile: the compiler's theorem {hTy}"
  let β := r.argsType
  let δ := r.resultType
  let modes := paramModes r.params r.modes
  let hF ← withLocalDeclD `y β fun y => do
    let a := mkApp f (mkApp r.flatArgs y)
    let get := a.headBeta
    let #[_, _, _, fv, env] := get.getAppArgs
      | throwError "verified_compile: the meaning {get}"
    let get' := get.replace fun e => if e.isConstOf funs then some funsVal else none
    let step ← mkExpectedTypeHint (← mkEqRefl a) (← mkEq a get')
    let chain ← getChain funsVal fv env
    let some (_, _, b) := (← inferType chain).eq?
      | throwError "verified_compile: the meaning of {get}"
    let c := mkApp r.flatResult (mkApp F y)
    let projs ← argProjsE y modes r.params.length
    let eq ← mkExpectedTypeHint (mkAppN (mkConst r.meaningEq) projs.toArray) (← mkEq b c)
    mkLambdaFVars #[y] (← transHint (← transHint step chain) eq)
  return mkAppN (mkConst ``ImplementsA.transferAgree)
    #[α, β, γ, δ, ia, ← userInst β, ic, ← userInst δ, aborts, m, entry, f, h, r.flatArgs,
      r.flatResult, F, hF, mkConst argsAgree, mkConst resultAgree]

/-- The most positions that the reflector accepts in a function whose code takes the call depth.
Wasmtime 44 on aarch64 keeps 8 bytes for each value live across a call and 16 bytes per frame, so
`depthLimit` frames of 32 positions take about 280 KB of its 512 KiB default stack, and the rest
holds the functions without the depth parameter at the top of the chain.  The example
`Recursion.deep` runs a frame of 32 positions, each live across the self-call, at depth 999 under
two such functions. -/
def depthPositions : Nat := 32

/-- Rejects a function whose code takes the call depth and needs more than `depthPositions`
positions, from its body `body`. -/
def checkPositions (name : Name) (body : Lean.Expr) : MetaM Unit := do
  let n ← kernelWhnf (← mkAppM ``positions #[body, toExpr true])
  let some k := natOf n
    | throwError "verified_compile: cannot evaluate the positions of {name}"
  if k > depthPositions then
    throwError "verified_compile: the code of {name} takes the call depth and needs {k} \
      positions, more than the {depthPositions} that {depthLimit} nested calls may use"

/-- `FVar.there (… (FVar.there FVar.here))` with `k` applications of `there`. -/
def fvarStx : Nat → CommandElabM Term
  | 0 => `(Verified.FVar.here)
  | k + 1 => do `(Verified.FVar.there $(← fvarStx k))

syntax (name := verifiedCompile) "verified_compile " ident " := " "[" ident,* "]" : command

/-- `verified_compile p := [f, g, …]` adds the program `p.program` of the listed definitions, in
order, each of which may call those before it and, when recursive, itself; the meanings
`p.funs` of its functions and the proof `p.meaning : Prog.Meaning p.program p.funs`; the module
`p.module`; for each definition `f`, the theorem `p.f.implements` that the module computes `f`,
at the function's index, or at its exported entry when its code takes the call depth; and
`p.bytes`, the module's bytes with all those theorems. -/
@[command_elab verifiedCompile]
def elabVerifiedCompile : CommandElab
  | `(verified_compile $target := [$sources,*]) => do
    let names ← sources.getElems.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let base := (← getCurrNamespace) ++ target.getId
    let (reflected, funsVal) ← liftTermElabM do
      let mut sigs : List Sig := []
      let mut prog := Lean.mkConst ``Prog.nil
      let mut funs := Lean.mkConst ``Funs.nil
      let mut meaning := Lean.mkConst ``Prog.Meaning.nil
      let mut out : Array Reflected := #[]
      let mut callees : List Callee := []
      for name in names do
        let sigsExpr := listExpr (Lean.mkConst ``Sig) (sigs.map sigExpr)
        let fbase := base ++ Name.mkSimple name.getString!
        let f := Lean.mkConst (fbase ++ `func)
        let r ← match ← getUnfoldEqnFor? name with
          | none =>
            let r ← reflectDefinition fbase name sigsExpr funs callees
            if r.depth then checkPositions name (mkApp2 (mkConst ``Func.body) sigsExpr f)
            let sig := sigExpr ⟨r.params, r.result, r.aborts, r.modes, r.depth⟩
            meaning := mkAppN (Lean.mkConst ``Prog.Meaning.cons) #[sigsExpr, f, prog, funs, meaning]
            funs := mkAppN (Lean.mkConst ``Funs.cons) #[sigsExpr, sig,
              mkAppN (Lean.mkConst ``Func.denote) #[sigsExpr, f, funs], funs]
            prog := mkAppN (Lean.mkConst ``Prog.cons) #[sigsExpr, f, prog]
            pure r
          | some eqName =>
            let r ← reflectRecursive fbase name eqName sigsExpr funs prog meaning callees
            checkPositions name (mkApp2 (mkConst ``RecFunc.body) sigsExpr f)
            let sig := sigExpr ⟨r.params, r.result, r.aborts, r.modes, r.depth⟩
            let M := Lean.mkConst (fbase ++ `meaning)
            meaning := mkAppN (Lean.mkConst ``Prog.Meaning.consRec)
              #[sigsExpr, f, prog, funs, M, meaning, Lean.mkConst (fbase ++ `fixed)]
            funs := mkAppN (Lean.mkConst ``Funs.cons) #[sigsExpr, sig, M, funs]
            prog := mkAppN (Lean.mkConst ``Prog.consRec) #[sigsExpr, f, prog]
            pure r
        let sig : Sig := ⟨r.params, r.result, r.aborts, r.modes, r.depth⟩
        sigs := sig :: sigs
        callees := ⟨name, sig, r.meaningEq⟩ :: callees
        out := out.push r
      let sigsExpr := listExpr (Lean.mkConst ``Sig) (sigs.map sigExpr)
      addDefinition (base ++ `program) (mkApp (Lean.mkConst ``Prog) sigsExpr) prog
      addDefinition (base ++ `funs) (mkApp (Lean.mkConst ``Funs) sigsExpr) funs
      addTheorem (base ++ `meaning)
        (mkApp3 (Lean.mkConst ``Prog.Meaning) sigsExpr (Lean.mkConst (base ++ `program))
          (Lean.mkConst (base ++ `funs))) meaning
      addDefinition (base ++ `module) (Lean.mkConst ``Wasm.Module)
        (← mkAppM ``compile #[Lean.mkConst (base ++ `program)])
      return (out, funs)
    let progId := mkIdent (base ++ `program)
    let funsId := mkIdent (base ++ `funs)
    let meaningId := mkIdent (base ++ `meaning)
    let moduleId := mkIdent (base ++ `module)
    let n := reflected.size
    let mut claims : Array Term := #[]
    let mut proofs : Array Term := #[]
    let mut entries := 0
    for k in [0:n] do
      let r := reflected[k]!
      let simple := Name.mkSimple r.name.getString!
      let implName := base ++ simple ++ `implements
      let fvar ← fvarStx (n - 1 - k)
      -- The compiler's theorem at the function's index, or at its entry, the `j`-th, when its
      -- code takes the call depth.
      let (hStx, index) ← if r.depth then
          let j := entries
          entries := entries + 1
          pure (← `(Verified.Prog.correct_entry $progId $funsId $meaningId $fvar rfl
            (j := $(Lean.quote j)) (by decide +kernel)), 2 + n + j)
        else
          pure (← `((Verified.Prog.correct $progId $funsId $meaningId $fvar).1 rfl), 2 + k)
      -- The theorem for the flattened types, carried to Lean's types: each argument is
      -- represented as its flattening is, and the flattening of the result represents it.
      liftTermElabM do
        let h ← Term.elabTerm (← `(Verified.ImplementsA.lean $hStx)) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let h ← instantiateMVars h
        let F ← withLocalDeclD `x r.argsType fun x => do
          let projs ← argProjsE x (paramModes r.params r.modes) r.params.length
          mkLambdaFVars #[x] (mkAppN (mkConst r.name) projs.toArray)
        let proof ← implementsProof (base ++ `funs) funsVal h F r (base ++ simple ++ `argsAgree)
          (base ++ simple ++ `resultAgree)
        -- The statement with the trap flag, the module, and the index as constants.
        let ty ← inferType proof
        let args := ty.getAppArgs
        let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr r.aborts)
          |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit index))
        addTheorem implName claim proof
      claims := claims.push (← `(type_of% $(mkIdent implName)))
      proofs := proofs.push (mkIdent implName)
    let bytesId := mkIdent (target.getId ++ `bytes)
    let conj ← claims.pop.foldrM (fun c acc => `($c ∧ $acc)) claims.back!
    let impls ← proofs.pop.foldrM (fun p acc => `(⟨$p, $acc⟩)) proofs.back!
    elabCommand (← `(theorem $bytesId : ∃ bytes, Wasm.Encoding.encode $moduleId = .ok bytes ∧
        Wasm.Encoding.decode bytes = .ok $moduleId ∧ $conj := by
      obtain ⟨bytes, success, decoded⟩ :=
        Wasm.Encoding.round_trip $moduleId (by decide +kernel) (by decide +kernel)
      exact ⟨bytes, success, decoded, $impls⟩))
  | _ => throwUnsupportedSyntax

end Verified.Reflect
