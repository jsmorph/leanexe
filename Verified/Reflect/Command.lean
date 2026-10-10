import Verified.Correct
import Verified.Instantiate
import Verified.Reflect.Lemmas
import Verified.Reflect.BoundPass
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
pairs, and structures whose `Flat` tuple holds arrays, which are represented as that tuple and split
as pairs are.  Its body may also hold arrays of tuples, which have no `Represent` instance.  A
structure's source value is its flattening `φ`, the source value of its `Flat` tuple, an array's is
the array of its elements' flattenings, and each equation states that the source expression means
`φ` of the Lean term, with `φ` the identity for the types without structures.  The theorem follows
from the equation by `ImplementsA.transferAgree`, with proofs that Lean's instances agree with the
source instances along `φ`.  Its body may use literals, its parameters, `let`, the word operations
`+`, `-`, `*`, `/`, `%`, `&&&`, `|||`, `^^^`, `<<<`, and `>>>`, the comparisons `==`, `!=`, `<`,
`≤`, `>`, `≥`, `=`, and `≠` as `Bool` values, `!`, `&&`, and `||`, `if` on a `Bool` or on a
comparison, also as `if h : c` with branches that do not use `h`, pairs built with `(a, b)` and
taken apart with `.1`, `.2`, or `match`, structures built with their constructor or `{ s with … }`
and taken apart with their fields or `match`, enumeration constructors, `Flat.flat` of enumerations,
`match` on enumerations, and `==`, `!=`, `decide`, and `if` on them, `LeanExe.loop`,
`LeanExe.repeatWhile`, `xs.size.toUInt64`, `xs[i.toNat]!`, `xs.set! i.toNat v`, `xs.push v`,
`xs ++ ys`, `LeanExe.build`, `LeanExe.insertAt xs i v`, `LeanExe.eraseAt xs i`, safe named
constants whose type holds no array, as their values, calls of the listed definitions before it,
and, in a recursive definition, calls of itself.  A definition
`f x := g T₁ … Tₖ x` that applies a listed definition `g` to constants `Tᵢ` of type `Array UInt64`
before its own parameters is a wrapper: the module holds the tables `Tᵢ` in data segments and
exports `f` as an entry that passes their addresses to `g`. -/

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
    unless sβ.ty matches .elem _ do
      -- A structure that holds arrays is split as its tuple, which must be a pair of all its
      -- fields.
      let some (ctor, _) ← structOf? type
        | throwError "verified_compile: {type} holds arrays and is not a structure"
      let (``Prod, _) := (← whnfR β).getAppFnArgs
        | throwError "verified_compile: the `Flat` instance of {type} holds arrays and is not a \
            pair"
      unless (← flatTree type β inst ctor).length == ctor.numFields do
        throwError "verified_compile: the `Flat` instance of {type} does not hold all its fields"
    let f ← withLocalDeclD `x type fun x => do
      mkLambdaFVars #[x] (sβ.apply (mkApp4 (mkConst ``LeanExe.Pipeline.Flat.flat) type β inst x))
    return ⟨sβ.ty, some f⟩
  throwError "verified_compile: the type {type} is not UInt64, Bool, Float, a structure with a \
    `Flat` instance, an array, or a pair"

def tyOf (type : Lean.Expr) : MetaM Ty := return (← shapeOf type).ty

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

/-- The allocation bound of a listed definition whose code takes no call depth: `p.g.bound`, and
the name of `p.g.bound_eq` when the equation gives a numeral, which a caller's bound then shows. -/
structure CalleeBound where
  bound : Name
  numeralEq : Option Name
  deriving Inhabited

/-- A listed definition that a later one may call: its name, its signature, its equation
`∀ args, Func.denote … = name args`, and its bound when its code takes no call depth. -/
structure Callee where
  name : Name
  sig : Sig
  denoteEq : Name
  bound? : Option CalleeBound := none

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
  /-- The bounds `Prog.bounds prog funs` of the functions before the definition, and the chain
  `prog` of those functions, which the bound of a call walks; `none` in a recursive definition,
  whose code takes the call depth and has no bound. -/
  bounds : Option Lean.Expr := none
  prog : Option Lean.Expr := none

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

/-- `e` with each projection of a pair `(a, b)` or of a structure's constructor at its head
replaced by the component, and each pair `(y.1, y.2)` of the components of `y` replaced by `y`,
from the inside out.  Each step is a reduction or eta for pairs, so the result is equal to `e` by
`rfl`. -/
partial def projReduce (e : Lean.Expr) : MetaM Lean.Expr := do
  let e := e.consumeMData.headBeta
  match e.getAppFnArgs with
  | (``Prod.fst, #[_, _, p]) => match (← projReduce p).getAppFnArgs with
    | (``Prod.mk, #[_, _, a, _]) => projReduce a
    | _ => return e
  | (``Prod.snd, #[_, _, p]) => match (← projReduce p).getAppFnArgs with
    | (``Prod.mk, #[_, _, _, b]) => projReduce b
    | _ => return e
  | (``Prod.mk, #[α, β, a, b]) =>
    let a ← projReduce a
    let b ← projReduce b
    if let (``Prod.fst, #[_, _, y]) := a.getAppFnArgs then
      if let (``Prod.snd, #[_, _, y']) := b.getAppFnArgs then
        if y == y' then return y
    return mkApp4 e.getAppFn α β a b
  | _ =>
    let some (i, p) ← structProj? e | return e
    let p ← projReduce p
    let .const k _ := p.getAppFn | return e
    let some (.ctorInfo ctor) := (← getEnv).find? k | return e
    unless p.getAppNumArgs == ctor.numParams + ctor.numFields do return e
    projReduce (p.getArg! (ctor.numParams + i))

/-- The `Flat` tuple of the fields of `e`, an application of a structure's constructor, built
along the tuple tree of its instance. -/
partial def ctorTuple? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
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
  let rec build (pre : List Bool) (ty : Lean.Expr) : MetaM Lean.Expr := do
    if let some (i, _) := tree.find? (·.2 == pre.reverse) then return fields[i]!
    let ty ← whnfR ty
    let (``Prod, #[a, b]) := ty.getAppFnArgs
      | throwError "verified_compile: the `Flat` instance of {type} is not a tuple of its fields"
    mkAppM ``Prod.mk #[← build (false :: pre) a, ← build (true :: pre) b]
  return some (← build [] β)

/-- Whether a Lean term reflects to a place: a variable, a pair of places, or a structure's
constructor whose tuple of fields is a place, as `reflectStruct?` reflects it. -/
partial def isPlace (e : Lean.Expr) : MetaM Bool := do
  let e ← projReduce e
  if e.isFVar then return true
  if let (``Prod.mk, #[_, _, a, b]) := e.getAppFnArgs then
    return (← isPlace a) && (← isPlace b)
  if let some tuple ← ctorTuple? e then return ← isPlace tuple
  return false

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

/-- The component of the tuple `x` along `steps`: `false` for a pair's first component and `true`
for its second. -/
def tuplePath (x : Lean.Expr) : List Bool → MetaM Lean.Expr
  | [] => return x
  | false :: rest => do tuplePath (← mkAppM ``Prod.fst #[x]) rest
  | true :: rest => do tuplePath (← mkAppM ``Prod.snd #[x]) rest

/-- A pair or a record that holds arrays, viewed as a pair for its destructuring: the component
types `α` and `β` of `α × β` or of the record's `Flat` tuple, the value built from components `a`
and `b`, the pair `pair p` of a value `p`, `p` itself or `Flat.flat p`, and the proof `eta B v` of
`B (rebuild (pair v).1 (pair v).2) = B v`. -/
structure PairView where
  α : Lean.Expr
  β : Lean.Expr
  rebuild : Lean.Expr → Lean.Expr → MetaM Lean.Expr
  pair : Lean.Expr → Lean.Expr
  eta : Lean.Expr → Lean.Expr → MetaM Lean.Expr

/-- The view of `type` as a pair.  A pair's eta is `pair_eta`.  A record's is the theorem
`base.flat_eta.R`, added once per program and record type and proved by `rfl` with `B` and `v`
free, so that the kernel unfolds only the `Flat` instance and structure eta, never the terms that
`B` and `v` stand for. -/
def pairView (base : Name) (type : Lean.Expr) : MetaM PairView := do
  let type ← whnfR type
  if let (``Prod, #[α, β]) := type.getAppFnArgs then
    return ⟨α, β, fun a b => mkAppM ``Prod.mk #[a, b], id, fun B v => mkAppM ``pair_eta #[B, v]⟩
  let some (ctor, _) ← structOf? type
    | throwError "verified_compile: {type} is not a pair or a record"
  let some (τ, inst) ← flatInstance? type
    | throwError "verified_compile: the record {type} has no `Flat` instance"
  let (``Prod, #[α, β]) := (← whnfR τ).getAppFnArgs
    | throwError "verified_compile: the `Flat` instance of {type} is not a pair"
  let tree ← flatTree type τ inst ctor
  let rebuild (a b : Lean.Expr) : MetaM Lean.Expr := do
    let fields ← (List.range ctor.numFields).mapM fun i => do
      match tree.find? (·.1 == i) with
      | some (_, false :: rest) => tuplePath a rest
      | some (_, true :: rest) => tuplePath b rest
      | _ => throwError "verified_compile: the `Flat` instance of {type} does not hold field {i}"
    return mkAppN (mkConst ctor.name type.getAppFn.constLevels!) (type.getAppArgs ++ fields.toArray)
  let pair (p : Lean.Expr) := mkApp4 (mkConst ``LeanExe.Pipeline.Flat.flat) type τ inst p
  let .const n _ := type.getAppFn | throwError "verified_compile: the record {type}"
  let name := base ++ `flat_eta ++ n
  unless (← getEnv).contains name do
    let (stmt, proof) ← withLocalDeclD `γ (mkSort levelOne) fun γ => do
      withLocalDeclD `B (← mkArrow type γ) fun B => withLocalDeclD `v type fun v => do
        let P := pair v
        let lhs := mkApp B (← rebuild (← mkAppM ``Prod.fst #[P]) (← mkAppM ``Prod.snd #[P]))
        let rhs := mkApp B v
        let proof ← mkExpectedTypeHint (← mkEqRefl rhs) (← mkEq lhs rhs)
        return (← mkForallFVars #[γ, B, v] (← mkEq lhs rhs), ← mkLambdaFVars #[γ, B, v] proof)
    addTheorem name stmt proof
  let eta (B v : Lean.Expr) : MetaM Lean.Expr := do
    return mkApp3 (mkConst name) (← inferType (mkApp B v)) B v
  return ⟨α, β, rebuild, pair, eta⟩

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

/-- `d` expanded along its product type into the pairs of its projections. -/
partial def expandPairs (d : Lean.Expr) : MetaM Lean.Expr := do
  let (``Prod, _) := (← whnfR (← inferType d)).getAppFnArgs | return d
  mkAppM ``Prod.mk
    #[← expandPairs (← mkAppM ``Prod.fst #[d]), ← expandPairs (← mkAppM ``Prod.snd #[d])]

/-- The arguments that the one alternative of the match `app` receives for the discriminant `d`,
a tuple, along the alternative's pattern, which may take nested pairs apart: the match on `d`
expanded into pairs reduces to the alternative applied to them. -/
def matchFields (app : MatcherApp) (d : Lean.Expr) : MetaM (Array Lean.Expr) := do
  withLocalDeclD `h (← inferType app.alts[0]!) fun h => do
    let .reduced v ← reduceMatcher? { app with discrs := #[← expandPairs d], alts := #[h] }.toExpr
      | throwError "verified_compile: cannot reduce the match {app.toExpr}"
    unless v.getAppFn == h do
      throwError "verified_compile: the match {app.toExpr} gives {v}"
    v.getAppArgs.mapM projReduce

/-- For a match `app` with one discriminant `d` of a structure type, `Prod` included, and one
alternative `alt`, the proof of `alt (fields d) = app`.  It is proved by `rfl` for a variable for
`d` and a variable for the alternative, since structure eta lets the match reduce on a variable,
also when the pattern takes nested pairs apart, and then applied to both, so that the kernel
evaluates neither the value nor the alternative's body. -/
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
    -- `refl` proves the goal by `Eq.refl lhs`, whose type omits the match, so a hint states it.
    let eq ← mkEq lhs rhs
    let goal ← mkFreshExprMVar eq
    goal.mvarId!.refl
    mkLambdaFVars #[h, s] (← mkExpectedTypeHint (← instantiateMVars goal) eq)
  return mkApp2 gen alt d

/-- From `proof : X = flatValue a` and `eq : a = e`, the proof of `X = flatValue e`. -/
def restate (proof eq : Lean.Expr) : MetaM Lean.Expr := do
  let some (_, _, e) := (← inferType eq).eq? | throwError "verified_compile: the equation {eq}"
  match (← shapeOf (← inferType e)).flat with
  | none => transHint proof eq
  | some f => transHint proof (← mkCongrArg f eq)

/-- A reflected Lean term: the source expression `src`, the proof that it means the flattening of
the Lean term `lean`, the source type, and the builder of its allocation bound. -/
structure Reflection where
  src : Lean.Expr
  proof : Lean.Expr
  ty : Ty
  lean : Lean.Expr
  bound : BoundBuilder

instance : Inhabited Reflection := ⟨⟨default, default, .word, default, noBound⟩⟩

/-- `r` as the reflection of the Lean term `e`, with the proof `proof` that its source means it. -/
def Reflection.as (r : Reflection) (proof e : Lean.Expr) : Reflection :=
  { r with proof, lean := e }

/-- `r` as the reflection of the Lean term `e`, whose flattening its proof already states up to
the kernel's reduction. -/
def Reflection.as' (r : Reflection) (e : Lean.Expr) : Reflection :=
  { r with lean := e }

/-- The proof that the source of `r` means the flattening of its Lean term, stated with that
term.  The meaning lemmas state an operation as `BinOp.apply` and a variable through the
environment, which the kernel reduces to the term. -/
def userProof (c : Ctx) (r : Reflection) : MetaM Lean.Expr := do
  mkExpectedTypeHint r.proof (← mkEq (← denoteExpr c r.src) (← flatValue r.lean))

/-- The arguments that the bound lemmas take from the context. -/
def boundArgs (c : Ctx) (bounds modes live : Lean.Expr) : List (Name × Lean.Expr) :=
  [(`S, c.sigs), (`Γ, c.ctx), (`funs, c.funs), (`bounds, bounds), (`modes, modes), (`live, live),
    (`env, c.env)]

/-- `e = e'` for `e` a cost that the bound lemmas build from sums, `if`s, and terms that charge
blocks, and `e'` the cost without its summands `0`, with `0` for an `if` whose branches are `0`,
for `sumBelow` of `0` and `loopCost` of a loop whose condition and body cost `0`, and with
`blockCost a` for `blockCost (a * 1)`.  It descends only through `+` and `if` on `Nat`, so it never
changes a Lean term of the user's, which appear only inside the charges.  `none` when nothing
changes. -/
partial def normCost (e : Lean.Expr) : MetaM (Lean.Expr × Option Lean.Expr) := do
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) =>
    let op := e.appFn!.appFn!
    unless op == natAdd do return (e, none)
    let (a', ha?) ← normCost a
    let (b', hb?) ← normCost b
    let step? ← if ha?.isNone && hb?.isNone then pure none
      else some <$> congr2 op a a' b b' ha? hb?
    let drop? : Option (Lean.Expr × Lean.Expr) ←
      if isNatZero b' then pure (some (a', ← mkAppM ``Nat.add_zero #[a']))
      else if isNatZero a' then pure (some (b', ← mkAppM ``Nat.zero_add #[b']))
      else pure none
    match step?, drop? with
    | none, none => return (e, none)
    | some s, none => return (mkApp2 op a' b', some s)
    | none, some (r, d) => return (r, some d)
    | some s, some (r, d) => return (r, some (← mkEqTrans s d))
  | (``ite, #[α, cond, inst, a, b]) =>
    unless α.isConstOf ``Nat do return (e, none)
    let iteFn := e.appFn!.appFn!
    let (a', ha?) ← normCost a
    let (b', hb?) ← normCost b
    let step? ← if ha?.isNone && hb?.isNone then pure none
      else some <$> congr2 iteFn a a' b b' ha? hb?
    if isNatZero a' && isNatZero b' then
      let self ← mkAppOptM ``ite_self #[some α, some cond, some inst, some natZero]
      match step? with
      | none => return (natZero, some self)
      | some s => return (natZero, some (← mkEqTrans s self))
    match step? with
    | none => return (e, none)
    | some s => return (mkApp2 iteFn a' b', some s)
  | (``sumBelow, #[f, n]) =>
    unless f.isLambda && isNatZero f.bindingBody! do return (e, none)
    let h ← withLocalDeclD `k (mkConst ``Nat) fun k => do
      mkLambdaFVars #[k] (← mkEqRefl natZero)
    return (natZero, some (← mkAppOptM ``sumBelow_zero #[some f, some h, some n]))
  | (``loopCost, #[α, CA, C, BA, F, n, i, s]) =>
    unless CA.isLambda && isNatZero CA.bindingBody! && BA.isLambda && BA.bindingBody!.isLambda &&
        isNatZero BA.bindingBody!.bindingBody! do return (e, none)
    let hCA ← withLocalDeclD `s α fun x => do mkLambdaFVars #[x] (← mkEqRefl natZero)
    let hBA ← withLocalDeclD `i (mkConst ``UInt64) fun j => withLocalDeclD `s α fun x => do
      mkLambdaFVars #[j, x] (← mkEqRefl natZero)
    return (natZero, some (← mkAppOptM ``loopCost_eq_zero
      #[some α, some CA, some C, some BA, some F, some hCA, some hBA, some n, some i, some s]))
  | (``blockCost, #[x]) =>
    let some (a, h) ← mulOne? x | return (e, none)
    let f := e.getAppFn
    return (mkApp f a, some (← congrArgOn f x a h))
  | _ => return (e, none)

/-- `e` with its head reduced once when it projects an application of a structure's constructor,
or, for a pair `(y.1, y.2)` of the projections of one term `y`, `y`. -/
def projStep? (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  if let some (i, p) ← structProj? e then
    let .const k _ := p.getAppFn | return none
    let some (.ctorInfo ctor) := (← getEnv).find? k | return none
    unless p.getAppNumArgs == ctor.numParams + ctor.numFields do return none
    return some (p.getArg! (ctor.numParams + i))
  let (``Prod.mk, #[_, _, a, b]) := e.getAppFnArgs | return none
  let (``Prod.fst, #[_, _, y]) := a.getAppFnArgs | return none
  let (``Prod.snd, #[_, _, y']) := b.getAppFnArgs | return none
  return if y == y' then some y else none

/-- The fields of `e`, an application of the constructor of a structure, or `none`. -/
def ctorFields? (e : Lean.Expr) : MetaM (Option (Array Lean.Expr)) := do
  let .const k _ := e.getAppFn | return none
  let some (.ctorInfo ctor) := (← getEnv).find? k | return none
  unless isStructure (← getEnv) ctor.induct do return none
  unless e.getAppNumArgs == ctor.numParams + ctor.numFields do return none
  return some (e.getAppArgs.extract ctor.numParams e.getAppNumArgs)

/-- The maximal parts of `e` that are not applications of a structure's constructor. -/
partial def ctorLeaves (e : Lean.Expr) : MetaM (Array Lean.Expr) := do
  match ← ctorFields? e with
  | some fs => fs.foldlM (fun acc f => return acc ++ (← ctorLeaves f)) #[]
  | none => return #[e]

/-- `e` with its leaves, from position `i` on, replaced by the terms `ys`, and the next position. -/
partial def ctorRebuild (e : Lean.Expr) (ys : Array Lean.Expr) (i : Nat) :
    MetaM (Lean.Expr × Nat) := do
  let some fs ← ctorFields? e | return (ys[i]!, i + 1)
  let mut j := i
  let mut fs' := #[]
  for f in fs do
    let (f', j') ← ctorRebuild f ys j
    fs' := fs'.push f'
    j := j'
  return (mkAppN e.getAppFn (e.getAppArgs.extract 0 (e.getAppNumArgs - fs.size) ++ fs'), j)

/-- `e` with each projection of an application of a structure's constructor reduced, and each pair
`(y.1, y.2)` replaced by `y`, where the term holds a variable of the current context.  The kernel
checks the reduction, behind a hint at this context, by comparing pairs of terms of which one holds
that variable, and it evaluates the operands of `Nat` operations only in pairs of closed terms.  A
variable that a lambda inside `e` binds is bound at the hint, so it does not count. -/
def reduceOpenProjs (e : Lean.Expr) : MetaM Lean.Expr := do
  let lctx ← getLCtx
  Meta.transform e (post := fun x => do
    unless x.hasAnyFVar lctx.contains do return .done x
    return .done ((← projStep? x).getD x))

/-- `b`, abstracted over variables, at the values `vs`: its proof applied to them, and its cost
instantiated with them, with the projections reduced that a value built in place leaves in it.
The reduction runs with the values' leaves as new variables, as `reduceOpenProjs` requires, and the
proof, abstracted over the variables, is applied to the leaves, which the kernel instantiates
without comparing anything. -/
def Bound.at (b : Bound) (vs : Array Lean.Expr) : MetaM Bound := do
  let plain : Bound := ⟨b.cost.beta vs, mkAppN b.proof vs⟩
  unless ← vs.anyM fun v => return (← ctorFields? v).isSome do return plain
  let leaves ← vs.foldlM (fun acc v => return acc ++ (← ctorLeaves v)) #[]
  let decls ← leaves.mapIdxM fun i l => do
    return ((`y).appendIndexAfter i, fun _ => inferType l)
  withLocalDeclsD decls fun ys => do
    let mut j := 0
    let mut vs' := #[]
    for v in vs do
      let (v', j') ← ctorRebuild v ys j
      vs' := vs'.push v'
      j := j'
    let cost := b.cost.beta vs'
    let reduced ← reduceOpenProjs cost
    if reduced == cost then return plain
    let p := mkAppN b.proof vs'
    let (lhs, _) ← eqSides p
    let h ← mkExpectedTypeHint p (← mkEq lhs reduced)
    return ⟨(← mkLambdaFVars ys reduced).beta leaves, mkAppN (← mkLambdaFVars ys h) leaves⟩

/-- The bound that `p : allocs = rhs` gives, with `rhs` normalized by `normCost` and its projections
of values built in place reduced by `reduceOpenProjs`. -/
def boundOf (p : Lean.Expr) : MetaM Bound := do
  let (lhs, rhs) ← eqSides p
  let (rhs', h?) ← normCost rhs
  let p ← match h? with | some h => mkEqTrans p h | none => pure p
  let reduced ← reduceOpenProjs rhs'
  if reduced == rhs' then return ⟨rhs', p⟩
  return ⟨reduced, ← mkExpectedTypeHint p (← mkEq lhs reduced)⟩

/-- The size of the Lean array `u`, whose flattening is the source value `v` of an array of
elements `e`, with the proof of `v.size = u.size`. -/
def arraySizeEq (e : Elem) (v u : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let (``Array, #[α]) := (← whnfR (← inferType u)).getAppFnArgs
    | throwError "verified_compile: the size of {u}, which is not an array"
  let n ← mkAppM ``Array.size #[u]
  let sizeV := mkApp2 (mkConst ``Array.size [Level.zero]) (mkApp (mkConst ``Elem.denote)
    (elemExpr e)) v
  match (← shapeOf α).flat with
  | none => return (n, ← mkExpectedTypeHint (← mkEqRefl n) (← mkEq sizeV n))
  | some φ => do
    let h ← mkAppOptM ``Array.size_map #[none, none, some φ, some u]
    return (n, ← mkExpectedTypeHint h (← mkEq sizeV n))

/-- The proof of `t.copyCost v = C` for the source value `v` of the Lean term `u`, with `C` written
with `blockCost` of the sizes of `u`'s arrays. -/
partial def copyCostEq (base : Name) (t : Ty) (v u : Lean.Expr) :
    MetaM (Lean.Expr × Lean.Expr) := do
  let lhs := mkApp2 (mkConst ``Ty.copyCost) (tyExpr t) v
  match t with
  | .elem _ => return (natZero, ← evalEq lhs natZero)
  | .array e =>
    let width := mkApp (mkConst ``Elem.width) (elemExpr e)
    let w ← evalNat width
    let hw ← evalEq width w
    let (n, hn) ← arraySizeEq e v u
    let p ← (← LemmaApp.start ``copyCost_array
      [(`e, elemExpr e), (`xs, v), (`hn, hn), (`hw, hw)]).finish
    let (_, cost) ← eqSides p
    let some (a, h) ← mulOne? cost.appArg! | return (cost, p)
    return (mkApp cost.appFn! a, ← mkEqTrans p (← congrArgOn cost.appFn! cost.appArg! a h))
  | .pair a b =>
    let view ← pairView base (← inferType u)
    let P := view.pair u
    let u1 ← projReduce (← mkAppM ``Prod.fst #[P])
    let u2 ← projReduce (← mkAppM ``Prod.snd #[P])
    let (_, ha) ← copyCostEq base a (← mkAppM ``Prod.fst #[v]) u1
    let (_, hb) ← copyCostEq base b (← mkAppM ``Prod.snd #[v]) u2
    let b ← boundOf (← (← LemmaApp.start ``copyCost_pair
      [(`a, tyExpr a), (`b, tyExpr b), (`v, v), (`ha, ha), (`hb, hb)]).finish)
    return (b.cost, b.proof)

/-- The proof of `coerceCost t s M v = K` for the source value `v` of the Lean term `u`, where the
modes `s` and `M` are closed terms: a copy when `s` is borrowed and `M` owned. -/
def coerceEq (base : Name) (t : Ty) (s M v u : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let common := [(`t, tyExpr t), (`s, s), (`m, M), (`v, v)]
  if let .elem e := t then
    return (natZero, ← (← LemmaApp.start ``coerce_elem
      [(`e, elemExpr e), (`s, s), (`m, M), (`v, v)]).finish)
  if ← evalOwned m!"the mode of {u}" s then
    return (natZero, ← (← LemmaApp.start ``coerce_owned
      (common ++ [(`hs, ← evalEq s (modeConst true))])).finish)
  unless ← evalOwned m!"the mode that {u} takes" M do
    return (natZero, ← (← LemmaApp.start ``coerce_borrowed
      (common ++ [(`hm, ← evalEq M (modeConst false))])).finish)
  let (C, hc) ← copyCostEq base t v u
  return (C, ← (← LemmaApp.start ``coerce_copy (common ++
    [(`hs, ← evalEq s (modeConst false)), (`hm, ← evalEq M (modeConst true)),
      (`hc, hc)])).finish)

/-- Assigns the mode argument `name` of `app`, which equation `hName` determines from a closed
mode term, the value that the kernel computes. -/
def assignMode (app : LemmaApp) (name hName : Name) : MetaM Lean.Expr := do
  let ty ← app.hypType hName
  let some (_, mode, _) := ty.eq?
    | throwError "verified_compile: the argument {hName} of {app.name} is not an equation"
  let m := modeConst (← evalOwned m!"a mode in {app.name}" mode)
  app.assign name m
  app.assign hName (← evalEq mode m)
  return m

/-- Assigns the coercion argument `name` of `app`, `coerceCost t s M v = K`, for the Lean term `u`
whose flattening is `v`. -/
def assignCoerce (base : Name) (app : LemmaApp) (name : Name) (t : Ty) (u : Lean.Expr) :
    MetaM Bound := do
  let ty ← app.hypType name
  let some (_, lhs, _) := ty.eq?
    | throwError "verified_compile: the argument {name} of {app.name} is not an equation"
  let (``coerceCost, #[_, s, M, v]) := lhs.getAppFnArgs
    | throwError "verified_compile: the argument {name} of {app.name} is not a coercion"
  let (K, hk) ← coerceEq base t s M v u
  app.assign name hk
  return ⟨K, hk⟩

/-- Assigns the branch argument `name` of `app`, `a.allocs … + coerceCost t s M A = AA`, from the
branch's bound and its coercion. -/
def assignBranch (base : Name) (app : LemmaApp) (name : Name) (t : Ty) (r : Reflection) :
    MetaM (Option Bound) := do
  let ty ← app.hypType name
  let some (_, lhs, _) := ty.eq?
    | throwError "verified_compile: the argument {name} of {app.name} is not an equation"
  let (``HAdd.hAdd, #[_, _, _, _, allocs, coerce]) := lhs.getAppFnArgs
    | throwError "verified_compile: the argument {name} of {app.name} is not a branch"
  let (``Expr.allocs, #[_, _, _, modes, live, _, _, _, _]) := allocs.getAppFnArgs
    | throwError "verified_compile: the argument {name} of {app.name} is not a bound"
  let some b ← r.bound modes live | return none
  let (``coerceCost, #[_, s, M, v]) := coerce.getAppFnArgs
    | throwError "verified_compile: the argument {name} of {app.name} has no coercion"
  let (K, hk) ← coerceEq base t s M v r.lean
  let b ← boundOf
    (← congr2 lhs.appFn!.appFn! allocs b.cost coerce K (some b.proof) (some hk))
  app.assign name b.proof
  return some b

/-- The proof of `x.ownedCost modes live (env.get x) = C` for the array variable `x` whose Lean
variable is `u`: nothing when `x` is owned and dies, and a copy otherwise. -/
def varOwnedEq (c : Ctx) (modes live x : Lean.Expr) (t : Ty) (u : Lean.Expr) :
    MetaM Lean.Expr := do
  let v ← mkAppM ``Env.get #[c.env, x]
  let args := [(`Γ, c.ctx), (`modes, modes), (`live, live), (`t, tyExpr t), (`x, x), (`v, v)]
  let index ← mkAppM ``Var.index #[x]
  let mode ← mkAppM ``modeAt #[modes, index]
  if ← evalOwned m!"the mode of {u}" mode then
    let isLive := (mkApp live index).headBeta
    if ← evalBool m!"whether {u} is live" isLive then
      let (_, hc) ← copyCostEq c.base t v u
      return ← (← LemmaApp.start ``varOwned_copyLive (args ++
        [(`hm, ← evalEq mode (modeConst true)), (`hl, ← evalEq isLive (boolConst true)),
          (`hc, hc)])).finish
    return ← (← LemmaApp.start ``varOwned_move (args ++
      [(`hm, ← evalEq mode (modeConst true)),
        (`hl, ← evalEq isLive (boolConst false))])).finish
  let (_, hc) ← copyCostEq c.base t v u
  (← LemmaApp.start ``varOwned_copyBorrowed (args ++
    [(`hm, ← evalEq mode (modeConst false)), (`hc, hc)])).finish

/-- The proof of `x.roomCost modes live (env.get x) ext = C` for the array variable `x` of elements
`e` whose Lean variable is `u`: the growth of an owned array that dies, and a copy at the new
length otherwise. -/
def roomEq (c : Ctx) (modes live x : Lean.Expr) (e : Elem) (u ext : Lean.Expr) :
    MetaM Bound := do
  let v ← mkAppM ``Env.get #[c.env, x]
  let (n, hn) ← arraySizeEq e v u
  let width := mkApp (mkConst ``Elem.width) (elemExpr e)
  let w ← evalNat width
  let args := [(`Γ, c.ctx), (`modes, modes), (`live, live), (`e, elemExpr e), (`x, x), (`xs, v),
    (`ext, ext), (`n, n), (`w, w), (`hn, hn), (`hw, ← evalEq width w)]
  let index ← mkAppM ``Var.index #[x]
  let mode ← mkAppM ``modeAt #[modes, index]
  let p ← if ← evalOwned m!"the mode of {u}" mode then do
      let isLive := (mkApp live index).headBeta
      if ← evalBool m!"whether {u} is live" isLive then
        (← LemmaApp.start ``room_copyLive (args ++
          [(`hm, ← evalEq mode (modeConst true)),
            (`hl, ← evalEq isLive (boolConst true))])).finish
      else
        (← LemmaApp.start ``room_grow (args ++
          [(`hm, ← evalEq mode (modeConst true)),
            (`hl, ← evalEq isLive (boolConst false))])).finish
    else
      (← LemmaApp.start ``room_copyBorrowed (args ++
        [(`hm, ← evalEq mode (modeConst false))])).finish
  let (_, cost) ← eqSides p
  -- `charge (n * 1 + ext)` is `charge (n + ext)`.
  let charge := cost.appFn!
  let arg := cost.appArg!
  let (``HAdd.hAdd, #[_, _, _, _, m, ext']) := arg.getAppFnArgs
    | throwError "verified_compile: the room {cost}"
  let some (a, hm) ← mulOne? m | return ⟨cost, p⟩
  let add := arg.appFn!.appFn!
  let h ← congrArgOn charge arg (mkApp2 add a ext') (← congr2 add m a ext' ext' (some hm) none)
  return ⟨mkApp charge (mkApp2 add a ext'), ← mkEqTrans p h⟩

/-- Assigns the extension `k` of a push or an insertion of an element `e`, with its proof
`(wordCount e.width).toNat = k`, the literal that the kernel computes. -/
def assignExtension (app : LemmaApp) (e : Elem) : MetaM Lean.Expr := do
  let ext ← mkAppM ``UInt64.toNat #[← mkAppM ``wordCount #[mkApp (mkConst ``Elem.width)
    (elemExpr e)]]
  let k ← evalNat ext
  app.assign `k k
  app.assign `hk (← evalEq ext k)
  return k

/-- The builder of a binary form with the lemma `n` over the parts `l` and `r`. -/
def binBound (c : Ctx) (n : Name) (args : List (Name × Lean.Expr)) (l r : Reflection) :
    BoundBuilder := fun modes live => do
  let some bounds := c.bounds | return none
  let app ← LemmaApp.start n (boundArgs c bounds modes live ++ args ++ [(`l, l.src), (`r, r.src)])
  let some _ ← app.child `hl l.bound | return none
  let some _ ← app.child `hr r.bound | return none
  boundOf (← app.finish)

/-- The builder of a unary form with the lemma `n` over the part `x`. -/
def unBound (c : Ctx) (n : Name) (args : List (Name × Lean.Expr)) (x : Reflection) :
    BoundBuilder := fun modes live => do
  let some bounds := c.bounds | return none
  let app ← LemmaApp.start n (boundArgs c bounds modes live ++ args ++ [(`e, x.src)])
  let some _ ← app.child `h x.bound | return none
  boundOf (← app.finish)

/-- The builder of a leaf with the lemma `n`, whose bound is `0`. -/
def leafBound (c : Ctx) (n : Name) (args : List (Name × Lean.Expr)) : BoundBuilder :=
  fun modes live => do
    let some bounds := c.bounds | return none
    let app ← LemmaApp.start n (boundArgs c bounds modes live ++ args)
    return some ⟨natZero, ← app.finish⟩

/-- The builder of the variable `x` of type `t`, whose Lean variable is `u`: a copy when it is
owned and live after the use. -/
def varBound (c : Ctx) (x : Lean.Expr) (t : Ty) (u : Lean.Expr) : BoundBuilder :=
  fun modes live => do
    let some bounds := c.bounds | return none
    let args := boundArgs c bounds modes live ++ [(`x, x)]
    if let .elem _ := t then
      return some ⟨natZero, ← (← LemmaApp.start ``var_elem_bound args).finish⟩
    let index ← mkAppM ``Var.index #[x]
    let mode ← mkAppM ``modeAt #[modes, index]
    unless ← evalOwned m!"the mode of {u}" mode do
      return some ⟨natZero, ← (← LemmaApp.start ``var_borrowed_bound
        (args ++ [(`hm, ← evalEq mode (modeConst false))])).finish⟩
    let isLive := (mkApp live index).headBeta
    unless ← evalBool m!"whether {u} is live" isLive do
      return some ⟨natZero, ← (← LemmaApp.start ``var_dead_bound
        (args ++ [(`hl, ← evalEq isLive (boolConst false))])).finish⟩
    let (C, hc) ← copyCostEq c.base t (← mkAppM ``Env.get #[c.env, x]) u
    return some ⟨C, ← (← LemmaApp.start ``var_copy_bound (args ++
      [(`hm, ← evalEq mode (modeConst true)), (`hl, ← evalEq isLive (boolConst true)),
        (`hc, hc)])).finish⟩

/-- A reflection under binders: the body's reflection, with its proof abstracted over the
binders and its bound not, and the binders with their declarations, which a bound restores. -/
structure Under where
  r : Reflection
  xs : Array Lean.Expr
  decls : List LocalDecl

/-- The bound of `u`'s body, abstracted over its binders. -/
def Under.bound (u : Under) : BoundBuilder := fun modes live => withExistingLocalDecls u.decls do
  let some b ← u.r.bound modes live | return none
  return some ⟨← mkLambdaFVars u.xs b.cost, ← mkLambdaFVars u.xs b.proof⟩

/-- The `∀` hypothesis `ty` over `u`'s binders, instantiated at them. -/
def Under.instantiate (u : Under) (ty : Lean.Expr) : MetaM Lean.Expr :=
  instantiateForall ty u.xs

/-- Checks the hint between `own`, the chain's `Func.bound S g fs (rest.bounds fs) env`, and
`target`, a callee's bound `p.g.bound tuple`.  The kernel unfolds `p.g.bound`, the higher
definition, to `Func.bound` at `Env.ofArgs` and compares the two applications argument by argument,
which needs every argument but the environment identical: a difference in another would make it
unfold `Func.bound` on both sides and evaluate the callee's bound. -/
def checkBoundTarget (what : MessageData) (own target : Lean.Expr) : MetaM Unit := do
  let unfolded := (← unfoldDefinition target).headBeta
  let a := own.getAppArgs
  let b := unfolded.getAppArgs
  unless own.getAppFn == unfolded.getAppFn && a.size == b.size && a.pop == b.pop do
    throwError "verified_compile: the bound of {what} does not match its callee's bound"
  unless ← isDefEq a.back! b.back! do
    throwError "verified_compile: the arguments of {what} do not match its callee's bound"

/-- The right-nested tuple of `xs`, `()` for none, with each owned array as `Moved`. -/
def argsTuple : List (Lean.Expr × Bool) → MetaM Lean.Expr
  | [] => return mkConst ``Unit.unit
  | [(x, owned)] => if owned then mkAppM ``LeanExe.Pipeline.Moved.mk #[x] else return x
  | (x, owned) :: rest => do
    let x ← if owned then mkAppM ``LeanExe.Pipeline.Moved.mk #[x] else pure x
    mkAppM ``Prod.mk #[x, ← argsTuple rest]

/-- The proof that the bounds `Prog.bounds prog funs` give the function that `fv` names its own
bound, `f.bound fs (rest.bounds fs) env`, by `bounds_get_there` and `bounds_get_here`, for chains
`prog` of `Prog.cons` and `Prog.consRec` and `funs` of `Funs.cons`. -/
partial def boundsChain (prog funs fv env : Lean.Expr) : MetaM Lean.Expr := do
  let (``Funs.cons, #[S, _, F, fs]) := funs.getAppFnArgs
    | throwError "verified_compile: the meanings {funs}"
  match fv.getAppFnArgs, prog.getAppFnArgs with
  | (``FVar.here, _), (``Prog.cons, #[_, f, rest]) =>
    return mkAppN (mkConst ``bounds_get_here) #[S, f, rest, F, fs, env]
  | (``FVar.there, #[_, g, _, v]), (``Prog.cons, #[_, f, rest]) =>
    transHint (mkAppN (mkConst ``bounds_get_there) #[S, g, f, rest, F, fs, v, env])
      (← boundsChain rest fs v env)
  | (``FVar.there, #[_, g, _, v]), (``Prog.consRec, #[_, f, rest]) =>
    transHint (mkAppN (mkConst ``bounds_get_thereRec) #[S, g, f, rest, F, fs, v, env])
      (← boundsChain rest fs v env)
  | _, _ => throwError "verified_compile: the function reference {fv} in {prog}"

/-- The source expression for the Lean term `e`, with the proof that it means `e`, its type, and
the builder of its bound.  An array that a reader reads and an argument with arrays that is not a
place are bound with `let` first.  A `let` of a place is replaced by its body with the place for
the variable, and every variable of a pair type is split into variables for its components, so
that a projection reads a component and a use of the whole is the pair of the components. -/
partial def reflect (c : Ctx) (e : Lean.Expr) : MetaM Reflection := do
  let e ← projReduce e
  if e.isFVar then
    let (x, t) ← varOf c e
    let src ← mkAppOptM ``Expr.var #[some c.sigs, some c.ctx, some (tyExpr t), some x]
    return ⟨src, ← rflProof c src (← flatValue e), t, e, varBound c x t e⟩
  if let some r := ← reflectCall? e then return r
  if let some r := ← reflectStruct? e then return r
  let shape ← shapeOf (← inferType e)
  if let some w ← enumWord? e then
    let src ← mkAppOptM ``Expr.word #[some c.sigs, some c.ctx, some w]
    return ⟨src, ← rflProof c src (← flatValue e), .word, e,
      leafBound c ``word_bound [(`v, w)]⟩
  if !e.hasFVar && !e.hasLooseBVars && shape.flat.isNone then
    match shape.ty with
    | .word =>
      if (← wordLit? e).isSome then
        let src ← mkAppOptM ``Expr.word #[some c.sigs, some c.ctx, some e]
        return ⟨src, ← rflProof c src e, .word, e, leafBound c ``word_bound [(`v, e)]⟩
    | .bool =>
      if e.isConstOf ``Bool.true || e.isConstOf ``Bool.false then
        let src ← mkAppOptM ``Expr.bool #[some c.sigs, some c.ctx, some e]
        return ⟨src, ← rflProof c src e, .bool, e, leafBound c ``bool_bound [(`v, e)]⟩
    | .float =>
      if let some bits ← floatLit? e then
        let src ← mkAppOptM ``Expr.float #[some c.sigs, some c.ctx, some (toExpr bits)]
        let prop ← mkEq (← mkAppM ``Float.toBits #[e]) (toExpr bits)
        let dec ← mkDecide prop
        let h := mkApp3 (mkConst ``of_decide_eq_true) prop dec.appArg!
          (mkApp2 (mkConst ``Eq.refl [Level.one]) (mkConst ``Bool) (mkConst ``Bool.true))
        let proof ← mkAppOptM ``float_eq #[some c.sigs, some c.ctx, some c.funs, some c.env,
          some (toExpr bits), some e, some h]
        return ⟨src, proof, .float, e, leafBound c ``float_bound [(`bits, toExpr bits)]⟩
    | .elem (.prod _ _) | .pair _ _ | .array _ => pure ()
  -- A named constant that holds no array is its value, which the kernel unfolds to it.
  if let .const name lvls := e then
    if let .defnInfo info ← getConstInfo name then
      if info.safety == .safe && shape.ty.scalar then
        try
          return ← reflectAs (info.value.instantiateLevelParams info.levelParams lvls) e
        catch
          | .error ref msg =>
            throw (.error ref m!"verified_compile: in the value of the constant {name}: {msg}")
          | ex => throw ex
  if let .letE n type value body _ := e then
    if ← isPlace value then return ← reflectAs (body.instantiate1 value) e
    let s ← tyOf type
    if let .pair _ _ := s then
      let view ← pairView c.base type
      let r ← destructure c [] value fun a b => do
        return body.instantiate1 (← view.rebuild a b)
      -- The body at the value built from the value's components is the `let`, by the view's eta.
      let lam := Lean.mkLambda n .default type body
      let eta ← view.eta lam value
      let some (_, lhs, _) := (← inferType eta).eq? | throwError "verified_compile: {eta}"
      return r.as (← restate r.proof (← mkExpectedTypeHint eta (← mkEq lhs e))) e
    let rv ← reflect c value
    -- The value's equation states the value itself, so that the body's equation substitutes it.
    let hv ← mkExpectedTypeHint rv.proof
      (← mkEq (← denoteExpr c rv.src) (← flatValue value))
    let sv ← shapeOf type
    return ← withLocalDeclD `x type fun x => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (tyExpr s), some (sv.apply x), some c.env]
      let c' : Ctx := { c with vars := (x, s) :: c.vars, env := env' }
      let rb ← reflect c' (body.instantiate1 x)
      let ub : Under := ⟨rb, #[x], [← x.fvarId!.getDecl]⟩
      let hb ← mkLambdaFVars #[x] rb.proof
      let src ← mkAppM ``Expr.letE #[rv.src, rb.src]
      let proof ← if sv.flat.isNone then mkAppM ``letE_eq #[hv, hb]
        else mkAppM ``letE_flat_eq #[← sv.fn type, value, hv, hb]
      let bound : BoundBuilder := fun modes live => do
        let some bounds := c.bounds | return none
        let flatArgs ← match sv.flat with
          | none => pure []
          | some φ => pure [(`φ, φ), (`X, value)]
        let app ← LemmaApp.start (if sv.flat.isNone then ``letE_bound else ``letE_flat_bound)
          (boundArgs c bounds modes live ++ [(`v, rv.src), (`b, rb.src)] ++ flatArgs)
        let m ← assignMode app `m `hm
        app.assign `hv hv
        let some _ ← app.child `hva rv.bound | return none
        let some bb ← ub.bound (← mkAppM ``List.cons #[m, modes])
          (← mkAppM ``shift #[mkNatLit 1, live]) | return none
        app.assign `hba (← bb.at #[value]).proof
        boundOf (← app.finish)
      return ⟨src, ← restate proof (← bareEq (body.instantiate1 value) e), rb.ty, e, bound⟩
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
      -- A pair built in place whose pattern binds its two components becomes `let` bindings of
      -- the components.  A pattern that takes a component further apart binds the pair first, as
      -- for any other value.
      if (← projReduce d).isAppOf ``Prod.mk && app.altNumParams[0]! == 2 then
        let fs ← matchFields app d
        let lets ← withLetDecl `a (← inferType fs[0]!) fs[0]! fun a => do
          withLetDecl `b (← inferType fs[1]!) fs[1]! fun b => mkLetFVars #[a, b] (alt.beta #[a, b])
        return ← reflectAs lets e
      if let some (_, fields) ← structOf? (← inferType d) then
        -- The fields of a structure are its projections, of a variable bound to it first.
        let fieldsOf (y : Lean.Expr) : MetaM (Array Lean.Expr) := fields.mapM (mkProjection y)
        let r ← if ← isPlace d then reflect c (alt.beta (← fieldsOf d))
          else reflect c (← withLetDecl `t (← inferType d) d fun y => do
            mkLetFVars #[y] (alt.beta (← fieldsOf y)))
        return r.as (← restate r.proof (← casesEq app fieldsOf)) e
      if let .elem _ ← tyOf (← inferType d) then
        -- The components of a tuple are its projections, of a variable bound to it first.
        let r ←
          if (← projReduce d).isFVar then reflect c (alt.beta (← matchFields app d))
          else reflect c (← withLetDecl `t (← inferType d) d fun y => do
            mkLetFVars #[y] (alt.beta (← matchFields app y)))
        return r.as (← restate r.proof (← casesEq app (matchFields app))) e
      let r ← destructure c [] d fun a b => do
        return alt.beta (← matchFields app (← mkAppM ``Prod.mk #[a, b]))
      return r.as (← restate r.proof (← casesEq app (matchFields app))) e
  if let some (_, p) ← structProj? e then
    if (← structOf? (← inferType p)).isSome then return ← reflectProj e
  let (fn, args) := e.getAppFnArgs
  if let some op := binOp? fn then
    if args.size == 6 && (← isFloat args[0]!) then
      let some fop := fbinOp? fn
        | throwError "verified_compile: unsupported operation {fn} on Float"
      let rl ← reflect c args[4]!
      let rr ← reflect c args[5]!
      return ⟨← mkAppM ``Expr.fbin #[fop, rl.src, rr.src],
        ← mkAppM ``fbin_eq #[fop, rl.proof, rr.proof], .float, e,
        binBound c ``fbin_bound [(`op, fop)] rl rr⟩
    if args.size == 6 then
      let rl ← reflect c args[4]!
      let rr ← reflect c args[5]!
      return ⟨← mkAppM ``Expr.bin #[op, rl.src, rr.src],
        ← mkAppM ``bin_eq #[op, rl.proof, rr.proof], .word, e,
        binBound c ``bin_bound [(`op, op)] rl rr⟩
  match fn, args with
  | ``Decidable.decide, #[p, inst] =>
    if let (``Ne, #[_, a, b]) := p.consumeMData.getAppFnArgs then
      -- `decide (a ≠ b)` is `!decide (a = b)`.
      let notEq ← mkAppOptM ``decide_not #[some (← mkEq a b), none, some inst]
      let T ← mkAppM ``not #[← mkDecide (← mkEq a b)]
      return ← reflectVia T (← mkExpectedTypeHint (← mkEqSymm notEq) (← mkEq T e))
    if let some r ← enumDecide? p inst then return r
    if let some (op, a, b) ← fcomparison? p then return (← reflectFCmp op a b).as' e
    let some (op, a, b) ← comparison? p
      | throwError "verified_compile: unsupported decision {p}"
    return (← reflectCmp op a b).as' e
  | ``BEq.beq, #[α, inst, a, b] =>
    if let some r ← enumBEq? ``BEq.beq ``flat_beq α inst a b then return r
    let r ← if ← isFloat α then reflectFCmp .eq a b else reflectCmp .eq a b
    return r.as' e
  | ``bne, #[α, inst, a, b] =>
    if let some r ← enumBEq? ``bne ``flat_bne α inst a b then return r
    if ← isFloat α then
      let r ← reflectFCmp .eq a b
      return ⟨← mkAppM ``Expr.not #[r.src], ← mkAppM ``not_eq #[r.proof], .bool, e,
        unBound c ``not_bound [] r⟩
    return (← reflectCmp .ne a b).as' e
  | ``Neg.neg, #[α, _, x] =>
    unless ← isFloat α do throwError "verified_compile: unsupported negation {e}"
    return (← reflectFUnary (mkConst ``FUnOp.neg) x).as' e
  | ``Float.sqrt, #[x] => return (← reflectFUnary (mkConst ``FUnOp.sqrt) x).as' e
  | ``UInt64.toFloat, #[x] =>
    return (← reflectConv ``Expr.toFloat ``toFloat_eq ``toFloat_bound
      (mkConst ``ToFloat.convert) x .float).as' e
  | ``Float.ofBits, #[x] =>
    return (← reflectConv ``Expr.toFloat ``toFloat_eq ``toFloat_bound
      (mkConst ``ToFloat.ofBits) x .float).as' e
  | ``Float.toUInt64, #[x] =>
    return (← reflectConv ``Expr.toWord ``toWord_eq ``toWord_bound
      (mkConst ``ToWord.truncate) x .word).as' e
  | ``Float.toBits, #[x] =>
    return (← reflectConv ``Expr.toWord ``toWord_eq ``toWord_bound
      (mkConst ``ToWord.toBits) x .word).as' e
  | ``Float.abs, #[x] => return (← reflectFUnary (mkConst ``FUnOp.abs) x).as' e
  | ``Min.min, #[α, inst, a, b] | ``Max.max, #[α, inst, a, b] =>
    unless (← isFloat α) || (← whnfR α).isConstOf ``UInt64 do
      throwError "verified_compile: unsupported {fn} on {α}"
    -- `min` and `max` on floats and words are `if a ≤ b`, with operands that are not variables
    -- bound first.
    let bind := [false, false, !(← projReduce a).isFVar, !(← projReduce b).isFVar]
    if bind.any id then
      return ← reflectAs (← bindArgs e.getAppFn [α, inst, a, b] bind #[] #[]) e
    let cond ← mkAppM ``LE.le #[a, b]
    let t ← if fn == ``Min.min then mkAppM ``ite #[cond, a, b] else mkAppM ``ite #[cond, b, a]
    let r ← reflect c t
    return r.as (← mkExpectedTypeHint r.proof (← mkEq (← denoteExpr c r.src) e)) e
  | ``not, #[a] =>
    let r ← reflect c a
    return ⟨← mkAppM ``Expr.not #[r.src], ← mkAppM ``not_eq #[r.proof], .bool, e,
      unBound c ``not_bound [] r⟩
  | ``and, #[a, b] =>
    let rl ← reflect c a
    let rr ← reflect c b
    return ⟨← mkAppM ``Expr.and #[rl.src, rr.src], ← mkAppM ``and_eq #[rl.proof, rr.proof],
      .bool, e, binBound c ``and_bound [] rl rr⟩
  | ``or, #[a, b] =>
    let rl ← reflect c a
    let rr ← reflect c b
    return ⟨← mkAppM ``Expr.or #[rl.src, rr.src], ← mkAppM ``or_eq #[rl.proof, rr.proof],
      .bool, e, binBound c ``or_bound [] rl rr⟩
  | ``Prod.mk, #[_, _, a, b] =>
    let ra ← reflect c a
    let rb ← reflect c b
    if let (.elem ea, .elem eb) := (ra.ty, rb.ty) then
      return ⟨← mkAppM ``Expr.mk #[ra.src, rb.src], ← mkAppM ``mk_eq #[ra.proof, rb.proof],
        .elem (.prod ea eb), e, binBound c ``mk_bound [] ra rb⟩
    return ⟨← mkAppM ``Expr.pair #[ra.src, rb.src], ← mkAppM ``pair_eq #[ra.proof, rb.proof],
      .pair ra.ty rb.ty, e, pairBound ra rb⟩
  | ``LeanExe.Pipeline.Flat.flat, #[α, _, inst, a] =>
    let some (_, flatInst) ← enumFlat? α | throwError "verified_compile: unsupported term {e}"
    unless ← kernelDefEq inst flatInst do
      throwError "verified_compile: {e} uses a `Flat` instance other than {flatInst}"
    return (← reflect c a).as' e
  | ``Prod.fst, #[_, _, p] =>
    if let .elem _ ← tyOf (← inferType p) then reflectProj e
    else return (← destructure c [] p fun a _ => return a).as' e
  | ``Prod.snd, #[_, _, p] =>
    if let .elem _ ← tyOf (← inferType p) then reflectProj e
    else return (← destructure c [] p fun _ b => return b).as' e
  | ``dite, #[α, p, inst, a, b] =>
    -- `if h : p then a else b` whose branches do not use `h` is `if p then a else b`.
    let .lam _ _ ta _ := a.consumeMData | throwError "verified_compile: unsupported term {e}"
    let .lam _ _ tb _ := b.consumeMData | throwError "verified_compile: unsupported term {e}"
    if ta.hasLooseBVars || tb.hasLooseBVars then
      throwError "verified_compile: the branches of {e} use the hypothesis of the `if`"
    reflectAs (← mkAppOptM ``ite #[some α, some p, some inst, some ta, some tb]) e
  | ``ite, #[α, p, inst, a, b] =>
    if let some r ← enumIte? α p inst a b then return r
    let r ← reflectIte p a b
    let some φ := (← shapeOf α).flat | return r.as' e
    -- The `if` of the flattenings is the flattening of the `if`.
    let comm ← mkAppOptM ``apply_ite #[none, none, some φ, some p, some inst, some a, some b]
    return r.as (← mkEqTrans r.proof (← mkEqSymm comm)) e
  | ``LeanExe.loop, #[α, n, init, f] =>
    let rn ← reflect c n
    let ri ← reflect c init
    let u ← reflectUnder c [] (mkConst ``UInt64) α .word ri.ty fun i acc =>
      return f.beta #[i, acc]
    let rb := u.r
    let cs ← mkAppOptM ``Expr.bool
      #[some c.sigs, some (ctxExpr (ri.ty :: c.vars.map (·.2))), some (mkConst ``Bool.true)]
    let sa ← shapeOf α
    let src ← mkAppM ``Expr.loop #[rn.src, ri.src, cs, rb.src]
    let proof ← if sa.flat.isNone then mkAppM ``loop_eq #[rn.proof, ri.proof, rb.proof]
      else mkAppM ``loop_flat_eq #[← sa.fn α, init, f, rn.proof, ri.proof, rb.proof]
    -- The condition `true` costs nothing at every state, and means `true`.
    let condTrue ← withLocalDeclD `s α fun s => mkLambdaFVars #[s] (mkConst ``Bool.true)
    let bound := loopBound rn ri u cs α init condTrue
      (fun cTy => do
        withLocalDeclD `s α fun s => do
          mkExpectedTypeHint (← mkLambdaFVars #[s] (← mkEqRefl (mkConst ``Bool.true))) cTy)
      f (fun hcaTy bounds => do
        forallTelescope hcaTy fun xs eq => do
          let some (_, lhs, _) := eq.eq? | throwError "verified_compile: the condition of {e}"
          let args := lhs.getAppArgs
          let proof ← (← LemmaApp.start ``bool_bound [(`S, c.sigs), (`Γ, args[5]!),
            (`funs, c.funs), (`bounds, bounds), (`modes, args[3]!), (`live, args[4]!),
            (`env, args[8]!), (`v, mkConst ``Bool.true)]).finish
          return some (← mkLambdaFVars xs natZero, ← mkLambdaFVars xs proof))
    return ⟨src, ← mkExpectedTypeHint proof (← mkEq (← denoteExpr c src) (← flatValue e)),
      ri.ty, e, bound⟩
  | ``LeanExe.repeatWhile, #[α, n, init, cnd, step] =>
    let rn ← reflect c n
    let ri ← reflect c init
    let uc ← reflectUnder1 c α ri.ty fun acc => return cnd.beta #[acc]
    let rc := uc.r
    let u ← reflectUnder c [] (mkConst ``UInt64) α .word ri.ty fun _ acc =>
      return step.beta #[acc]
    let rb := u.r
    let sa ← shapeOf α
    let src ← mkAppM ``Expr.loop #[rn.src, ri.src, rc.src, rb.src]
    let proof ← if sa.flat.isNone then
        mkAppM ``repeatWhile_eq #[rn.proof, ri.proof, cnd, step, rc.proof, rb.proof]
      else mkAppM ``repeatWhile_flat_eq #[← sa.fn α, init, cnd, step, rn.proof, ri.proof,
        rc.proof, rb.proof]
    let F ← withLocalDeclD `i (mkConst ``UInt64) fun i => withLocalDeclD `s α fun s => do
      mkLambdaFVars #[i, s] (step.beta #[s])
    let bound := loopBound rn ri u rc.src α init cnd
      (fun cTy => do mkExpectedTypeHint rc.proof cTy) F
      (fun hcaTy _ => withExistingLocalDecls uc.decls do
        let ty ← uc.instantiate hcaTy
        let some (_, lhs, _) := ty.eq? | throwError "verified_compile: the condition of {e}"
        let args := lhs.getAppArgs
        let some b ← rc.bound args[3]! args[4]! | return none
        return some (← mkLambdaFVars uc.xs b.cost, ← mkLambdaFVars uc.xs b.proof))
    return ⟨src, ← mkExpectedTypeHint proof (← mkEq (← denoteExpr c src) (← flatValue e)),
      ri.ty, e, bound⟩
  | ``Array.set!, setArgs@#[α, xs, k, v] =>
    let se ← shapeOf α
    let .elem el := se.ty | throwError "verified_compile: unsupported array {e}"
    let (``UInt64.toNat, #[i]) := k.consumeMData.getAppFnArgs
      | throwError "verified_compile: a position must be `i.toNat` for a word `i`, in {e}"
    let xs ← projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (setArgs.set! 1 a))) e
    let (x, t) ← varOf c xs
    unless t == .array el do throwError "verified_compile: {xs} is not an array variable"
    let ri ← reflect c i
    let rv ← reflect c v
    let src ← mkAppOptM ``Expr.set
      #[some c.sigs, some c.ctx, none, some x, some ri.src, some rv.src]
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let app ← LemmaApp.start ``set_bound (boundArgs c bounds modes live ++
        [(`e, elemExpr el), (`x, x), (`i, ri.src), (`v, rv.src)])
      let some _ ← app.child `hi ri.bound | return none
      let some _ ← app.child `hv rv.bound | return none
      app.assign `hx (← varOwnedEq c modes live x (.array el) xs)
      boundOf (← app.finish)
    if se.flat.isNone then
      return ⟨src, ← mkAppM ``set_eq #[x, ri.proof, rv.proof], .array el, e, bound⟩
    return ⟨src,
      ← mkAppM ``set_map_eq #[← se.fn α, x, xs, v, ← arrayEq x xs, ri.proof, rv.proof],
      .array el, e, bound⟩
  | ``Array.push, pushArgs@#[α, xs, v] =>
    let se ← shapeOf α
    let .elem el := se.ty | throwError "verified_compile: unsupported array {e}"
    let xs ← projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (pushArgs.set! 1 a))) e
    let (x, t) ← varOf c xs
    unless t == .array el do throwError "verified_compile: {xs} is not an array variable"
    let rv ← reflect c v
    let src ← mkAppOptM ``Expr.push #[some c.sigs, some c.ctx, none, some x, some rv.src]
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let app ← LemmaApp.start ``push_bound (boundArgs c bounds modes live ++
        [(`e, elemExpr el), (`x, x), (`v, rv.src)])
      let k ← assignExtension app el
      let some _ ← app.child `hv rv.bound | return none
      app.assign `hx (← roomEq c modes live x el xs k).proof
      boundOf (← app.finish)
    if se.flat.isNone then
      return ⟨src, ← mkAppM ``push_eq #[x, rv.proof], .array el, e, bound⟩
    return ⟨src, ← mkAppM ``push_map_eq #[← se.fn α, x, xs, v, ← arrayEq x xs, rv.proof],
      .array el, e, bound⟩
  | ``LeanExe.insertAt, insertArgs@#[α, xs, k, v] =>
    let se ← shapeOf α
    let .elem el := se.ty | throwError "verified_compile: unsupported array {e}"
    let xs ← projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (insertArgs.set! 1 a))) e
    let (x, t) ← varOf c xs
    unless t == .array el do throwError "verified_compile: {xs} is not an array variable"
    let ri ← reflect c k
    let rv ← reflect c v
    let src ← mkAppOptM ``Expr.insertAt
      #[some c.sigs, some c.ctx, none, some x, some ri.src, some rv.src]
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let app ← LemmaApp.start ``insertAt_bound (boundArgs c bounds modes live ++
        [(`e, elemExpr el), (`x, x), (`i, ri.src), (`v, rv.src)])
      let k ← assignExtension app el
      let some _ ← app.child `hi ri.bound | return none
      let some _ ← app.child `hv rv.bound | return none
      app.assign `hx (← roomEq c modes live x el xs k).proof
      boundOf (← app.finish)
    if se.flat.isNone then
      return ⟨src, ← mkAppM ``insertAt_eq #[x, ri.proof, rv.proof], .array el, e, bound⟩
    return ⟨src, ← mkAppM ``insertAt_map_eq
      #[← se.fn α, x, xs, v, ← arrayEq x xs, ri.proof, rv.proof], .array el, e, bound⟩
  | ``LeanExe.eraseAt, eraseArgs@#[α, xs, k] =>
    let se ← shapeOf α
    let .elem el := se.ty | throwError "verified_compile: unsupported array {e}"
    let xs ← projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (eraseArgs.set! 1 a))) e
    let (x, t) ← varOf c xs
    unless t == .array el do throwError "verified_compile: {xs} is not an array variable"
    let ri ← reflect c k
    let src ← mkAppOptM ``Expr.eraseAt #[some c.sigs, some c.ctx, none, some x, some ri.src]
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let app ← LemmaApp.start ``eraseAt_bound (boundArgs c bounds modes live ++
        [(`e, elemExpr el), (`x, x), (`i, ri.src)])
      let some _ ← app.child `hi ri.bound | return none
      app.assign `hx (← varOwnedEq c modes live x (.array el) xs)
      boundOf (← app.finish)
    if se.flat.isNone then
      return ⟨src, ← mkAppM ``eraseAt_eq #[x, ri.proof], .array el, e, bound⟩
    return ⟨src, ← mkAppM ``eraseAt_map_eq #[← se.fn α, x, xs, ← arrayEq x xs, ri.proof],
      .array el, e, bound⟩
  | ``HAppend.hAppend, appendArgs@#[α, _, _, _, xs, ys] =>
    let .array el ← tyOf α | throwError "verified_compile: unsupported term {e}"
    let xs ← projReduce xs
    let ys ← projReduce ys
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
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let app ← LemmaApp.start ``append_bound (boundArgs c bounds modes live ++
        [(`e, elemExpr el), (`x, x), (`y, y)])
      let (ny, hny) ← arraySizeEq el (← mkAppM ``Env.get #[c.env, y]) ys
      let width := mkApp (mkConst ``Elem.width) (elemExpr el)
      let w ← evalNat width
      let some (_, prod, _) := (← app.hypType `hk).eq?
        | throwError "verified_compile: the extension of {e}"
      let (``HMul.hMul, #[_, _, _, _, size, _]) := prod.getAppFnArgs
        | throwError "verified_compile: the extension of {e}"
      let mul := prod.appFn!.appFn!
      let hk ← congr2 mul size ny width w (some hny) (some (← evalEq width w))
      let (k, hk) ← match ← mulOne? (mkApp2 mul ny w) with
        | some (a, h) => pure (a, ← mkEqTrans hk h)
        | none => pure (mkApp2 mul ny w, hk)
      app.assign `k k
      app.assign `hk hk
      let some (_, room, _) := (← app.hypType `hx).eq?
        | throwError "verified_compile: the room of {e}"
      let roomArgs := room.getAppArgs
      app.assign `hx (← roomEq c roomArgs[0]! roomArgs[1]! x el xs k).proof
      boundOf (← app.finish)
    if se.flat.isNone then return ⟨src, ← rflProof c src e, .array el, e, bound⟩
    return ⟨src, ← mkAppOptM ``append_map_eq #[some c.sigs, some c.ctx, some c.funs, some c.env,
      none, none, some (← se.fn β), some x, some y, some xs, some ys, some (← arrayEq x xs),
      some (← arrayEq y ys)], .array el, e, bound⟩
  | ``LeanExe.build, #[α, n, f] =>
    let se ← shapeOf α
    let .elem el := se.ty | throwError "verified_compile: unsupported array {e}"
    let rn ← reflect c n
    let (fs, hf, ue) ← withLocalDeclD `i (mkConst ``UInt64) fun i => do
      let env' ← mkAppOptM ``Env.cons #[some c.ctx, some (mkConst ``Ty.word), some i, some c.env]
      let c' : Ctx := { c with vars := (i, .word) :: c.vars, env := env' }
      let rf ← reflect c' (f.beta #[i])
      unless rf.ty == .elem el do throwError "verified_compile: an element of {e} is not a {α}"
      return (rf.src, ← mkLambdaFVars #[i] rf.proof,
        (⟨rf, #[i], [← i.fvarId!.getDecl]⟩ : Under))
    let src ← mkAppM ``Expr.build #[rn.src, fs]
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let app ← LemmaApp.start ``build_bound
        (boundArgs c bounds modes live ++ [(`count, rn.src), (`elem, fs)])
      let some (_, _, allRhs) := (← app.hypType `hall).eq?
        | throwError "verified_compile: the build {e}"
      app.assign `all allRhs
      app.assign `hall (← mkEqRefl allRhs)
      let width := mkApp (mkConst ``Elem.width) (elemExpr el)
      let w ← evalNat width
      app.assign `w w
      app.assign `hw (← evalEq width w)
      app.assign `hn (← userProof c rn)
      let some _ ← app.child `hna rn.bound | return none
      let some eb ← ue.bound (← mkAppM ``List.cons #[mkConst ``Mode.borrowed, modes])
        (← mkAppM ``shift #[mkNatLit 1, allRhs]) | return none
      -- The element's bound at the index `UInt64.ofNat k` of the sum.
      let (EA, hea) ← withLocalDeclD `k (mkConst ``Nat) fun k => do
        let b ← eb.at #[← mkAppM ``UInt64.ofNat #[k]]
        return (← mkLambdaFVars #[k] b.cost, ← mkLambdaFVars #[k] b.proof)
      app.assign `EA EA
      app.assign `hea hea
      boundOf (← app.finish)
    if se.flat.isNone then
      return ⟨src, ← mkAppM ``build_eq #[rn.proof, hf], .array el, e, bound⟩
    return ⟨src, ← mkAppM ``build_map_eq #[← se.fn α, f, rn.proof, hf], .array el, e,
      bound⟩
  | ``Nat.toUInt64, #[n] =>
    let (``Array.size, sizeArgs@#[_, xs]) := n.consumeMData.getAppFnArgs
      | throwError "verified_compile: unsupported term {e}"
    let xs ← projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn #[mkAppN n.consumeMData.getAppFn (sizeArgs.set! 1 a)])) e
    let (x, t) ← varOf c xs
    let .array _ := t | throwError "verified_compile: {xs} is not an array variable"
    let src ← mkAppOptM ``Expr.size #[some c.sigs, some c.ctx, none, some x]
    let (``Array, #[β]) := (← whnfR (← inferType xs)).getAppFnArgs
      | throwError "verified_compile: {xs} is not an array"
    let se ← shapeOf β
    let bound := leafBound c ``size_bound [(`x, x)]
    if se.flat.isNone then return ⟨src, ← rflProof c src e, .word, e, bound⟩
    return ⟨src, ← mkAppOptM ``size_map_eq #[some c.sigs, some c.ctx, some c.funs, some c.env,
      none, none, some (← se.fn β), some x, some xs, some (← arrayEq x xs)], .word, e, bound⟩
  | ``getElem!, getArgs@#[_, _, β, _, _, inh, xs, k] =>
    let (``UInt64.toNat, #[i]) := k.consumeMData.getAppFnArgs
      | throwError "verified_compile: an index must be `i.toNat` for a word `i`, in {e}"
    let xs ← projReduce xs
    unless xs.isFVar do
      return ← reflectAs (← withLetDecl `a (← inferType xs) xs fun a =>
        mkLetFVars #[a] (mkAppN e.getAppFn (getArgs.set! 6 a))) e
    let (x, t) ← varOf c xs
    let .array el := t | throwError "verified_compile: {xs} is not an array variable"
    let ri ← reflect c i
    let src ← mkAppOptM ``Expr.get #[some c.sigs, some c.ctx, none, some x, some ri.src]
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let app ← LemmaApp.start ``get_bound
        (boundArgs c bounds modes live ++ [(`x, x), (`i, ri.src)])
      let some _ ← app.child `hi ri.bound | return none
      boundOf (← app.finish)
    let se ← shapeOf β
    if se.flat.isNone then return ⟨src, ← mkAppM ``get_eq #[x, ri.proof], .elem el, e, bound⟩
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
      some (← se.fn β), some hd, some x, some xs, none, none, some (← arrayEq x xs),
      some ri.proof]
    return ⟨src, proof, .elem el, e, bound⟩
  | _, _ => throwError "verified_compile: unsupported term {e}"
where
  /-- The proof by `rfl` that the source value of the array variable `xs` is its flattening. -/
  arrayEq (x xs : Lean.Expr) : MetaM Lean.Expr := do
    let v ← flatValue xs
    mkExpectedTypeHint (← mkEqRefl v) (← mkEq (← mkAppM ``Env.get #[c.env, x]) v)
  /-- The builder of a loop over the count `rn` from the initial state `ri`, with the condition
`cond` and the body `u` under its index and state, for the Lean state type `α`, initial state
`init`, condition `C`, and step `F`.  `hc` proves the condition's meaning hypothesis, and
`condBound` gives its cost as a function of the state with the proof of its bound hypothesis. -/
  loopBound (rn ri : Reflection) (u : Under) (cond α init C : Lean.Expr)
      (hc : Lean.Expr → MetaM Lean.Expr) (F : Lean.Expr)
      (condBound : Lean.Expr → Lean.Expr → MetaM (Option (Lean.Expr × Lean.Expr))) :
      BoundBuilder := fun modes live => do
    let some bounds := c.bounds | return none
    let sa ← shapeOf α
    let flatArgs ← match sa.flat with
      | none => pure []
      | some φ => pure [(`φ, φ), (`I, init)]
    let thm := if sa.flat.isNone then ``loop_bound else ``loop_flat_bound
    let app ← LemmaApp.start thm (boundArgs c bounds modes live ++
      [(`count, rn.src), (`init, ri.src), (`cond, cond), (`body, u.r.src), (`C, C), (`F, F)] ++
      flatArgs)
    let some (_, _, allRhs) := (← app.hypType `hall).eq?
      | throwError "verified_compile: the loop's live variables"
    app.assign `all allRhs
    app.assign `hall (← mkEqRefl allRhs)
    let _ ← assignMode app `M `hM
    app.assign `hn (← userProof c rn)
    app.assign `hi (← userProof c ri)
    app.assign `hc (← hc (← app.hypType `hc))
    app.assign `hb (← mkExpectedTypeHint u.r.proof (← app.hypType `hb))
    let some _ ← app.child `hna rn.bound | return none
    let some _ ← app.child `hia ri.bound | return none
    let _ ← assignCoerce c.base app `hka ri.ty init
    let some (CA, hca) ← condBound (← app.hypType `hca) bounds | return none
    app.assign `CA CA
    app.assign `hca hca
    let hbaTy ← app.hypType `hba
    let some (cost, proof) ← withExistingLocalDecls u.decls do
        let ty ← u.instantiate hbaTy
        let some (_, lhs, _) := ty.eq? | throwError "verified_compile: the loop's body"
        let (``HAdd.hAdd, #[_, _, _, _, allocs, coerce]) := lhs.getAppFnArgs
          | throwError "verified_compile: the loop's body"
        let args := allocs.getAppArgs
        let some b ← u.r.bound args[3]! args[4]! | return none
        let (``coerceCost, #[_, s, M', v]) := coerce.getAppFnArgs
          | throwError "verified_compile: the loop's body"
        let value ← projReduce (F.beta u.xs)
        let (K, hk) ← coerceEq c.base ri.ty s M' v value
        let b ← boundOf
          (← congr2 lhs.appFn!.appFn! allocs b.cost coerce K (some b.proof) (some hk))
        return some (← mkLambdaFVars u.xs b.cost, ← mkLambdaFVars u.xs b.proof)
      | return none
    app.assign `BA cost
    app.assign `hba proof
    boundOf (← app.finish)
  /-- The builder of a pair, with the coercions of its components to the pair's mode. -/
  pairBound (ra rb : Reflection) : BoundBuilder := fun modes live => do
    let some bounds := c.bounds | return none
    let app ← LemmaApp.start ``pair_bound
      (boundArgs c bounds modes live ++ [(`a, ra.src), (`b, rb.src)])
    let _ ← assignMode app `M `hM
    app.assign `ha (← userProof c ra)
    app.assign `hb (← userProof c rb)
    let some _ ← app.child `haa ra.bound | return none
    let _ ← assignCoerce c.base app `hka ra.ty ra.lean
    let some _ ← app.child `hba rb.bound | return none
    let _ ← assignCoerce c.base app `hkb rb.ty rb.lean
    boundOf (← app.finish)
  /-- A structure built with its constructor: the tuple that its `Flat` instance makes of the
  fields, reflected as a tuple, whose meaning is the structure's flattening. -/
  reflectStruct? (e : Lean.Expr) : MetaM (Option Reflection) := do
    let some tuple ← ctorTuple? e | return none
    let r ← reflect c tuple
    return some (r.as (← mkExpectedTypeHint r.proof
      (← mkEq (← denoteExpr c r.src) (← flatValue e))) e)
  /-- `e`, reflected as the term `T` with `eq : T = e`. -/
  reflectVia (T eq : Lean.Expr) : MetaM Reflection := do
    let r ← reflect c T
    let some (_, _, e) := (← inferType eq).eq? | throwError "verified_compile: the equation {eq}"
    return r.as (← restate r.proof eq) e
  /-- The `LawfulBEq` instance of an enumeration, which `==` on it needs. -/
  enumLawful (α beq : Lean.Expr) : MetaM Lean.Expr := do
    let some inst ← synthInstance? (mkApp2 (mkConst ``LawfulBEq [Level.zero]) α beq)
      | throwError "verified_compile: `==` on {α} needs `LawfulBEq {α}`; derive `DecidableEq`, or \
          `BEq` and `LawfulBEq`"
    return inst
  /-- `==` or `!=` (the function `op`) on enumerations, as the same comparison of their words,
  by the lemma `thm`. -/
  enumBEq? (op thm : Name) (α inst a b : Lean.Expr) : MetaM (Option Reflection) := do
    let some (n, flatInst) ← enumFlat? α | return none
    let h ← flatInjective c.base n flatInst
    let lawful ← enumLawful α inst
    let flat := enumFlat n flatInst
    let eq ← mkAppOptM thm #[some α, some flatInst, some inst, some lawful, some h, some a, some b]
    return some (← reflectVia (← mkAppM op #[mkApp flat a, mkApp flat b]) (← mkEqSymm eq))
  /-- `decide (a = b)` on enumerations, as the same decision on their words. -/
  enumDecide? (p inst : Lean.Expr) : MetaM (Option Reflection) := do
    let (``Eq, #[_, a, b]) := p.consumeMData.getAppFnArgs | return none
    let some (n, flatInst) ← enumFlat? (← inferType a) | return none
    let h ← flatInjective c.base n flatInst
    let flat := enumFlat n flatInst
    let eq ← mkAppOptM ``flat_decide #[none, some flatInst, some h, some a, some b, some inst]
    let words ← mkEq (mkApp flat a) (mkApp flat b)
    return some (← reflectVia (← mkDecide words) (← mkEqSymm eq))
  /-- `e`, reflected as `T`, which equals it by `bareEq`. -/
  reflectAs (T e : Lean.Expr) : MetaM Reflection := do
    let r ← reflect c T
    return r.as (← restate r.proof (← bareEq T e)) e
  /-- `if a = b` and `if a ≠ b` on enumerations, as the same test on their words. -/
  enumIte? (α p inst x y : Lean.Expr) : MetaM (Option Reflection) := do
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
  reflectEnumMatch (app : MatcherApp) (n : Name) (inst : Lean.Expr) : MetaM Reflection := do
    let d := app.discrs[0]!
    unless (← projReduce d).isFVar do
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
  reflectIte (p a b : Lean.Expr) : MetaM Reflection := do
    let ra ← reflect c a
    let rb ← reflect c b
    let iteBound (thm : Name) (condArgs : List (Name × Lean.Expr))
        (conds : List (Name × Reflection)) (cond : BoundBuilder) : BoundBuilder :=
        fun modes live => do
      let some bounds := c.bounds | return none
      let app ← LemmaApp.start thm
        (boundArgs c bounds modes live ++ condArgs ++ [(`a, ra.src), (`b, rb.src)])
      let _ ← assignMode app `M `hM
      for (name, r) in conds do app.assign name (← userProof c r)
      app.assign `ha (← userProof c ra)
      app.assign `hb (← userProof c rb)
      let some _ ← app.child `hca cond | return none
      let some _ ← assignBranch c.base app `haa ra.ty ra | return none
      let some _ ← assignBranch c.base app `hba rb.ty rb | return none
      boundOf (← app.finish)
    match (p.consumeMData).getAppFnArgs with
    | (``Eq, #[α, cond, tru]) =>
      if (← whnfR α).isConstOf ``Bool && tru.isConstOf ``Bool.true then
        let rc ← reflect c cond
        return ⟨← mkAppM ``Expr.ite #[rc.src, ra.src, rb.src],
          ← mkAppM ``ite_eq #[rc.proof, ra.proof, rb.proof], ra.ty, a,
          iteBound ``ite_bound [(`c, rc.src)] [(`hc, rc)] rc.bound⟩
    | _ => pure ()
    if let some (op, l, r) ← fcomparison? p then
      let rl ← reflect c l
      let rr ← reflect c r
      let cond ← mkAppM ``Expr.fcmp #[fcmpExpr op, rl.src, rr.src]
      let (thm, bthm) ← match op with
        | .lt => pure (``ite_flt_eq, ``ite_flt_bound)
        | .le => pure (``ite_fle_eq, ``ite_fle_bound)
        | .eq => throwError "verified_compile: unsupported condition {p}"
      return ⟨← mkAppM ``Expr.ite #[cond, ra.src, rb.src],
        ← mkAppM thm #[rl.proof, rr.proof, ra.proof, rb.proof], ra.ty, a,
        iteBound bthm [(`l, rl.src), (`r, rr.src)] [(`hl, rl), (`hr, rr)]
          (binBound c ``fcmp_bound [(`op, fcmpExpr op)] rl rr)⟩
    let some (op, l, r) ← comparison? p
      | throwError "verified_compile: unsupported condition {p}"
    let rl ← reflect c l
    let rr ← reflect c r
    let cond ← mkAppM ``Expr.cmp #[cmpExpr op, rl.src, rr.src]
    let bthm := match op with
      | .lt => ``ite_lt_bound
      | .le => ``ite_le_bound
      | .eq => ``ite_eqP_bound
      | .ne => ``ite_ne_bound
    return ⟨← mkAppM ``Expr.ite #[cond, ra.src, rb.src],
      ← mkAppM (iteLemma op) #[rl.proof, rr.proof, ra.proof, rb.proof], ra.ty, a,
      iteBound bthm [(`l, rl.src), (`r, rr.src)] [(`hl, rl), (`hr, rr)]
        (binBound c ``cmp_bound [(`op, cmpExpr op)] rl rr)⟩
  /-- The reflection of `body` in the context `c`, with each variable of `xs` that has a pair
  type split first into its components. -/
  reflectSplit (c : Ctx) : List Lean.Expr → Lean.Expr → MetaM Reflection
    | [], body => reflect c body
    | x :: rest, body => do
      match ← tyOf (← inferType x) with
      | .pair _ _ =>
        let view ← pairView c.base (← inferType x)
        let r ← destructure c rest x fun a b => do
          return body.replaceFVar x (← view.rebuild a b)
        -- The body at the value built from `x`'s components is the body, by the view's eta.
        let P := view.pair x
        let split := body.replaceFVar x
          (← view.rebuild (← mkAppM ``Prod.fst #[P]) (← mkAppM ``Prod.snd #[P]))
        let eta ← view.eta (← mkLambdaFVars #[x] body) x
        return r.as (← restate r.proof (← mkExpectedTypeHint eta (← mkEq split body))) body
      | _ => reflectSplit c rest body
  /-- The reflection of `body a` with `a : α` of type `s` as variable 0, with its proof and its
  bound abstracted over `a`, which is split when it has a pair type. -/
  reflectUnder1 (c : Ctx) (α : Lean.Expr) (s : Ty) (body : Lean.Expr → MetaM Lean.Expr) :
      MetaM Under :=
    withLocalDeclD `a α fun a => do
      let env' ← mkAppOptM ``Env.cons
        #[some c.ctx, some (tyExpr s), some (← flatValue a), some c.env]
      let c' : Ctx := { c with vars := (a, s) :: c.vars, env := env' }
      let r ← reflectSplit c' [a] (← body a)
      let proof ← mkLambdaFVars #[a] r.proof
      return ⟨{ r with proof }, #[a], [← a.fvarId!.getDecl]⟩
  /-- The reflection of `body a b` with `a : α` of type `s` as variable 1 and `b : β` of type `t`
  as variable 0, with its proof and its bound abstracted over `a` and `b`.  The variables `a`,
  `b`, and `rest` that have pair types are split. -/
  reflectUnder (c : Ctx) (rest : List Lean.Expr) (α β : Lean.Expr) (s t : Ty)
      (body : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM Under :=
    withLocalDeclD `a α fun a => withLocalDeclD `b β fun b => do
      let envA ← mkAppOptM ``Env.cons
        #[some c.ctx, some (tyExpr s), some (← flatValue a), some c.env]
      let ctxA := ctxExpr (s :: c.vars.map (·.2))
      let envB ← mkAppOptM ``Env.cons
        #[some ctxA, some (tyExpr t), some (← flatValue b), some envA]
      let c' : Ctx := { c with vars := (b, t) :: (a, s) :: c.vars, env := envB }
      let r ← reflectSplit c' (b :: a :: rest) (← body a b)
      let proof ← mkLambdaFVars #[a, b] r.proof
      return ⟨{ r with proof }, #[a, b], [← a.fvarId!.getDecl, ← b.fvarId!.getDecl]⟩
  /-- A component of a tuple or a field of a structure, `e`, a chain of `Prod.fst`, `Prod.snd`,
  and structure projections: the projection of a variable along a path, with a value that is not
  a variable bound with `let` first.  Besides the base and the path, the walk returns the chain as
  a function of the base. -/
  reflectProj (e : Lean.Expr) : MetaM Reflection := do
    let rec walk (e : Lean.Expr) (steps : List Bool) :
        MetaM (Lean.Expr × List Bool × (Lean.Expr → MetaM Lean.Expr)) := do
      let e ← projReduce e
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
      return ⟨src, ← rflProof c src (← flatValue e), .elem target, e,
        leafBound c ``proj_bound [(`x, x), (`p, path)]⟩
    reflectAs (← withLetDecl `t (← inferType base) base fun y => do
      mkLetFVars #[y] (← chain y)) e
  /-- The destructuring of the pair or record `p` into the components `a` and `b` of its pair
  view, as variables 1 and 0 of the body `body a b`, in which the variables `rest` are split. -/
  destructure (c : Ctx) (rest : List Lean.Expr) (p : Lean.Expr)
      (body : Lean.Expr → Lean.Expr → MetaM Lean.Expr) : MetaM Reflection := do
    let rp ← reflect c p
    let .pair s t := rp.ty | throwError "verified_compile: {p} is not a pair"
    let view ← pairView c.base (← inferType p)
    let u ← reflectUnder c rest view.α view.β s t body
    let rb := u.r
    let sa ← shapeOf view.α
    let sb ← shapeOf view.β
    let src ← mkAppM ``Expr.letPair #[rp.src, rb.src]
    let flat := sa.flat.isSome || sb.flat.isSome
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let identity (α : Lean.Expr) : MetaM Lean.Expr :=
        withLocalDeclD `x α fun x => mkLambdaFVars #[x] x
      let flatArgs ← if flat then
          pure [(`φa, ← match sa.flat with | some f => pure f | none => identity view.α),
            (`φb, ← match sb.flat with | some f => pure f | none => identity view.β),
            (`P, view.pair p)]
        else pure []
      let app ← LemmaApp.start (if flat then ``letPair_flat_bound else ``letPair_bound)
        (boundArgs c bounds modes live ++ [(`e, rp.src), (`body, rb.src)] ++ flatArgs)
      let m ← assignMode app `m `hm
      app.assign `he (← userProof c rp)
      -- The components: those of a pair built in place, or the projections.
      let pair ← if flat then pure (view.pair p)
        else instantiateMVars app.mvars[← app.index `E]!
      let (A, B) ← match pair.getAppFnArgs with
        | (``Prod.mk, #[_, _, a, b]) => pure (a, b)
        | _ => do pure (← mkAppM ``Prod.fst #[pair], ← mkAppM ``Prod.snd #[pair])
      app.assign `A A
      app.assign `B B
      app.assign `hA (← mkEqRefl A)
      app.assign `hB (← mkEqRefl B)
      let some _ ← app.child `hea rp.bound | return none
      let some bb ← u.bound (← mkAppM ``List.cons #[m, ← mkAppM ``List.cons #[m, modes]])
        (← mkAppM ``shift #[mkNatLit 2, live]) | return none
      app.assign `hba (← bb.at #[A, B]).proof
      boundOf (← app.finish)
    if !flat then
      return ⟨src, ← mkAppM ``letPair_eq #[rp.proof, rb.proof], rb.ty, rb.lean, bound⟩
    return ⟨src, ← mkAppM ``letPair_flat_eq #[← sa.fn view.α, ← sb.fn view.β, view.pair p,
      rp.proof, rb.proof], rb.ty, rb.lean, bound⟩
  /-- A call of a listed definition before this one: the source call, with the proof built from
  the arguments' proofs and the callee's equation. -/
  reflectCall? (e : Lean.Expr) : MetaM (Option Reflection) := do
    let .const fn _ := e.getAppFn | return none
    let some j := c.callees.findIdx? (·.name == fn) | return none
    let some callee := c.callees[j]? | return none
    let args := e.getAppArgs
    unless args.size == callee.sig.params.length do
      throwError "verified_compile: {fn} must be applied to all {callee.sig.params.length} \
        arguments"
    let bind ← (args.toList.zip callee.sig.params).zipIdx.mapM fun ((a, t), i) => do
      if t.scalar then return false
      if callee.sig.mode i = .owned then return !(← projReduce a).isFVar
      return !(← isPlace a)
    if bind.any id then
      return some (← reflectAs (← bindArgs e.getAppFn args.toList bind #[] #[]) e)
    let reflected ← args.toList.mapM (reflect c)
    let nilArgs ← mkAppOptM ``Args.nil #[some c.sigs, some c.ctx]
    let argList ← reflected.foldrM (fun r acc => mkAppM ``Args.cons #[r.src, acc]) nilArgs
    let nilEq ← mkAppOptM ``ofFn_nil_eq #[some c.sigs, some c.ctx, some c.funs, some c.env]
    let hargs ← reflected.foldrM (fun r acc => mkAppM ``ofFn_cons_eq #[r.proof, acc]) nilEq
    let values ← envExpr (args.toList.zip callee.sig.params)
    let f ← fvarAt c.sigs j
    -- `funs.get f values` is the callee's meaning by `getChain`, and the callee's equation gives
    -- its value, with no unfolding of the callee's definition.
    let hf ← transHint (← getChain c.funs f values)
      (mkAppN (mkConst callee.denoteEq) args)
    let src ← mkAppM ``Expr.call #[f, ← mkAppM ``Args.get #[argList]]
    let bound : BoundBuilder := fun modes live => do
      let some bounds := c.bounds | return none
      let some prog := c.prog | return none
      let some cb := callee.bound? | return none
      let app ← LemmaApp.start ``call_bound
        (boundArgs c bounds modes live ++ [(`f, f), (`argList, argList)])
      for (name, h) in [(`all, `hall), (`kept, `hkept)] do
        let some (_, _, rhs) := (← app.hypType h).eq?
          | throwError "verified_compile: the argument {h} of call_bound"
        app.assign name rhs
        app.assign h (← mkEqRefl rhs)
      app.assign `hargs hargs
      let some (_, sumLhs, _) := (← app.hypType `hsum).eq?
        | throwError "verified_compile: the argument hsum of call_bound"
      -- `ArgsCost funs bounds modes all kept env md argList`, with `md` third from the end.
      let sumArgs := sumLhs.getAppArgs
      unless sumLhs.isAppOf ``ArgsCost && sumArgs.size ≥ 6 do
        throwError "verified_compile: the arguments' bound {sumLhs}"
      let all := sumArgs[sumArgs.size - 6]!
      let kept := sumArgs[sumArgs.size - 5]!
      let md := sumArgs[sumArgs.size - 3]!
      let some hsum ← argsCostBound bounds modes all kept md (reflected.zip callee.sig.params)
        argList | return none
      app.assign `hsum hsum
      let some (_, getLhs, _) := (← app.hypType `hb).eq?
        | throwError "verified_compile: the argument hb of call_bound"
      let A := getLhs.appArg!
      let chain ← boundsChain prog c.funs f A
      let owned := (List.range args.size).map fun i => callee.sig.mode i == .owned &&
        !callee.sig.params[i]!.scalar
      let tuple ← argsTuple (args.toList.zip owned)
      let target := mkApp (mkConst cb.bound) tuple
      let some (_, _, chainRhs) := (← inferType chain).eq?
        | throwError "verified_compile: the bounds of {fn}"
      checkBoundTarget m!"{fn}" chainRhs target
      let hb ← mkExpectedTypeHint chain (← mkEq getLhs target)
      let hb ← match cb.numeralEq with
        | some n => mkEqTrans hb (mkAppN (mkConst n) args)
        | none => pure hb
      app.assign `hb hb
      boundOf (← app.finish)
    return some ⟨src, ← mkAppM ``call_eq #[f, hargs, hf], callee.sig.result, e, bound⟩
  /-- The proof of `ArgsCost funs bounds modes all kept env md argList = AS` for the arguments
  `args`, each with its parameter type. -/
  argsCostBound (bounds modes all kept md : Lean.Expr) (args : List (Reflection × Ty))
      (argList : Lean.Expr) : MetaM (Option Lean.Expr) := do
    let common := [(`S, c.sigs), (`Γ, c.ctx), (`funs, c.funs), (`bounds, bounds),
      (`modes, modes), (`all, all), (`kept, kept), (`env, c.env), (`md, md)]
    match args with
    | [] => return some (← (← LemmaApp.start ``argsCost_nil common).finish)
    | (r, t) :: rest =>
      let restList := argList.appArg!
      let parts := common ++ [(`e, r.src), (`rest, restList)]
      let scalar := mkApp (mkConst ``Ty.scalar) (tyExpr t)
      let app ← if t.scalar then do
          let app ← LemmaApp.start ``argsCost_scalar
            (parts ++ [(`ht, ← evalEq scalar (boolConst true))])
          let some (_, lhs, _) := (← app.hypType `he).eq?
            | throwError "verified_compile: the argument he of argsCost_scalar"
          let (``Expr.allocs, #[_, _, _, ms, lv, _, _, _, _]) := lhs.getAppFnArgs
            | throwError "verified_compile: the argument he of argsCost_scalar"
          let some b ← r.bound ms lv | return none
          app.assign `he b.proof
          pure app
        else do
          let m0 := (mkApp md (mkNatLit 0)).headBeta
          if ← evalOwned m!"the mode of a parameter" m0 then
            let app ← LemmaApp.start ``argsCost_owned (parts ++
              [(`ht, ← evalEq scalar (boolConst false)), (`hm, ← evalEq m0 (modeConst true))])
            let (``Expr.var, #[_, _, _, x]) := r.src.getAppFnArgs
              | throwError "verified_compile: an argument at an owned parameter is not a variable"
            app.assign `he (← (← LemmaApp.start ``ownedArg_var [(`S, c.sigs), (`Γ, c.ctx),
              (`modes, modes), (`env, c.env), (`x, x), (`kept, kept),
              (`h, ← varOwnedEq c modes kept x t r.lean)]).finish)
            pure app
          else
            LemmaApp.start ``argsCost_borrowed (parts ++
              [(`ht, ← evalEq scalar (boolConst false)), (`hm, ← evalEq m0 (modeConst false))])
      let some (_, lhs, _) := (← app.hypType `hr).eq?
        | throwError "verified_compile: the argument hr of the arguments' bound"
      let restArgs := lhs.getAppArgs
      unless lhs.isAppOf ``ArgsCost && restArgs.size ≥ 3 do
        throwError "verified_compile: the arguments' bound {lhs}"
      let md' := restArgs[restArgs.size - 3]!
      let some hr ← argsCostBound bounds modes all kept md' rest restList | return none
      app.assign `hr hr
      return some (← boundOf (← app.finish)).proof
  reflectCmp (op : CmpOp) (a b : Lean.Expr) : MetaM Reflection := do
    let rl ← reflect c a
    unless rl.ty == .word do
      throwError "verified_compile: comparisons apply to words, floats, and enumerations, not \
        {← inferType a}"
    let rr ← reflect c b
    return ⟨← mkAppM ``Expr.cmp #[cmpExpr op, rl.src, rr.src],
      ← mkAppM ``cmp_eq #[cmpExpr op, rl.proof, rr.proof], .bool, a,
      binBound c ``cmp_bound [(`op, cmpExpr op)] rl rr⟩
  reflectFCmp (op : FCmpOp) (a b : Lean.Expr) : MetaM Reflection := do
    let rl ← reflect c a
    let rr ← reflect c b
    return ⟨← mkAppM ``Expr.fcmp #[fcmpExpr op, rl.src, rr.src],
      ← mkAppM ``fcmp_eq #[fcmpExpr op, rl.proof, rr.proof], .bool, a,
      binBound c ``fcmp_bound [(`op, fcmpExpr op)] rl rr⟩
  reflectFUnary (op x : Lean.Expr) : MetaM Reflection := do
    let r ← reflect c x
    return ⟨← mkAppM ``Expr.funary #[op, r.src], ← mkAppM ``funary_eq #[op, r.proof], .float,
      x, unBound c ``funary_bound [(`op, op)] r⟩
  reflectConv (ctor thm bthm : Name) (op x : Lean.Expr) (t : Ty) : MetaM Reflection := do
    let r ← reflect c x
    return ⟨← mkAppM ctor #[op, r.src], ← mkAppM thm #[op, r.proof], t, x,
      unBound c bthm [(`op, op)] r⟩

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
  | .pair _ _, _ =>
    -- A record with arrays agrees as its `Flat` tuple does.
    let some (β, _) ← flatInstance? userT
      | throwError "verified_compile: the type {userT} does not have the shape of {tyExpr t}"
    let (_, proof) ← agreeTy β t
    agreeAs userT inst src φ
      (← mkAppOptM ``Agree.flat #[some userT, some β, none, none, none, none, none, some proof])
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
  /-- The bound, when the definition's code takes no call depth. -/
  bound? : Option CalleeBound := none
  deriving Inhabited

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
    flatResult, none⟩

/-- Reflects definition `name` as a function that may call the functions `sigs`, meaning
`funs`, of the program `prog`, with the parameter modes that `Expr.paramChoice` gives, and adds
`base.func` and `base.denote_eq`.  When its code takes no call depth, it also adds `base.bound`, the
function's allocation bound on Lean's tuple of its arguments, and `base.bound_eq`, which states the
bound as a Lean term in the parameters. -/
def reflectDefinition (base name : Name) (sigs funs prog : Lean.Expr) (callees : List Callee) :
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
    let bounds := mkAppN (mkConst ``Prog.bounds) #[sigs, prog, funs]
    let c : Ctx :=
      { base := base.getPrefix, sigs := sigs, funs := funs, callees := callees, vars := vars,
        env := env, bounds := some bounds, prog := some prog }
    let r ← reflect.reflectSplit c params.toList body
    let modes ← paramChoiceOf name r.src
    let funcType := mkApp (mkConst ``Func) sigs
    let func ← mkAppOptM ``Func.mk #[some sigs, some (toExpr name.getString!),
      some (ctxExpr types), some (tyExpr result), some r.src, some (← mkEqRefl (toExpr true)),
      some (modesExpr modes)]
    addDefinition (base ++ `func) funcType func
    let f := Lean.mkConst (base ++ `func)
    let lhs ← mkAppM ``Func.denote #[f, funs, env]
    let eqType ← mkForallFVars params
      (← mkEq lhs (resultShape.apply (mkAppN (mkConst name) params)))
    -- `name = fun params => body` by `rfl`: against a lambda the kernel can only unfold `name`.
    -- Applied to the parameters, it relates the body to `name params` by beta reduction, so the
    -- kernel never compares `name params` with a body headed by a matcher, which it would unfold
    -- first, evaluating the matcher's discriminant.
    let value ← instantiateMVars info.value
    let hdef ← mkExpectedTypeHint (← mkEqRefl (mkConst name)) (← mkEq (mkConst name) value)
    let happ ← params.foldlM (fun h p => mkCongrFun h p) hdef
    let full ← restate r.proof (← mkEqSymm happ)
    addTheorem (base ++ `denote_eq) eqType (← mkLambdaFVars params full)
    let aborts ← evalBool m!"whether {name} may trap" (← mkAppM ``Func.aborts #[f])
    let depth ← evalBool m!"whether the code of {name} takes the call depth"
      (← mkAppM ``Func.depth #[f])
    let reflected ← finishReflected base name params types result (← inferType body) aborts
      modes depth (base ++ `denote_eq)
    if depth then return reflected
    -- The bound: the compiler's bound of the function, among the functions before it, at the
    -- flattening of Lean's tuple of the arguments.  Its height above its value's makes the kernel
    -- unfold it, and not the compiler's bound, when it matches a statement with a proof.
    let ps := ctxExpr types
    let ms := modesExpr modes
    let boundName := base ++ `bound
    let boundVal ← withLocalDeclD `x reflected.argsType fun x => do
      mkLambdaFVars #[x] (mkAppN (mkConst ``Func.bound) #[sigs, f, funs, bounds,
        mkAppN (mkConst ``Env.ofArgs) #[ps, ms, (mkApp reflected.flatArgs x).headBeta]])
    addAndCompile <| .defnDecl <| mkDefinitionValEx boundName []
      (← mkArrow reflected.argsType (mkConst ``Nat)) boundVal
      (.regular (getMaxHeight (← getEnv) boundVal + 1)) .safe [boundName]
    let numeralEq ← boundEquation base name params types modes result func funs bounds env
      resultShape r
    return { reflected with bound? := some ⟨boundName, numeralEq⟩ }
where
  /-- Adds `base.bound_eq` from the body's bound at the entry modes, with nothing live after
  it, and the copy of a borrowed result.  `f` is the value of `base.func`, a `Func.mk`, whose
  projections reduce without unfolding it.  Returns `base.bound_eq` when the bound is a numeral,
  which a caller's bound then states in place of the call. -/
  boundEquation (base name : Name) (params : Array Lean.Expr) (types : List Ty)
      (modes : List Mode) (result : Ty) (f funs bounds env : Lean.Expr) (resultShape : Shape)
      (r : Reflection) : MetaM (Option Name) := do
    let some entry ← modesOf (← mkAppM ``entryModes #[ctxExpr types, modesExpr modes])
      | throwError "verified_compile: cannot evaluate the entry modes of {name}"
    let ms := modesExpr entry
    let app ← LemmaApp.start ``func_bound
      [(`func, f), (`args, env), (`funs, funs), (`bounds, bounds), (`ms, ms)]
    let some (_, entryModes, _) := (← app.hypType `hms).eq?
      | throwError "verified_compile: the entry modes of {name}"
    app.assign `hms (← evalEq entryModes ms)
    let call := mkAppN (mkConst name) params
    app.assign `V (resultShape.apply call)
    app.assign `hv (← mkExpectedTypeHint (mkAppN (mkConst (base ++ `denote_eq)) params)
      (← app.hypType `hv))
    let (bodyModes, live) ← app.allocsArgs `hba
    let some b ← r.bound bodyModes live
      | throwError "verified_compile: the body of {name} has no bound"
    app.assign `BA b.cost
    app.assign `hba (← mkExpectedTypeHint b.proof (← app.hypType `hba))
    -- The copy of a borrowed result, stated with the result's type and body as the terms of the
    -- function, which the kernel unfolds.
    let some (_, coerce, _) := (← app.hypType `hk).eq?
      | throwError "verified_compile: the result of {name}"
    let (``coerceCost, #[_, s, M, v]) := coerce.getAppFnArgs
      | throwError "verified_compile: the result of {name}"
    let (K, hk) ← coerceEq base.getPrefix result s M v call
    app.assign `KA K
    app.assign `hk (← mkExpectedTypeHint hk (← app.hypType `hk))
    let root ← boundOf (← app.finish)
    let (fbEnv, _) ← eqSides root.proof
    let owned := (paramModes types modes).map (· == .owned)
    let tuple ← argsTuple (params.toList.zip owned)
    let lhs := mkApp (mkConst (base ++ `bound)) tuple
    let step ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs fbEnv)
    let proof ← mkEqTrans step root.proof
    addTheorem (base ++ `bound_eq) (← mkForallFVars params (← mkEq lhs root.cost))
      (← mkLambdaFVars params proof)
    return if (natOf root.cost).isSome then some (base ++ `bound_eq) else none

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
  -- The structure built from a tuple `w` of its fields.
  let ctorOf (w : Lean.Expr) : MetaM Lean.Expr := do
    let fields ← (List.range ctor.numFields).mapM fun i => do
      let some (_, steps) := tree.find? (·.1 == i)
        | throwError "verified_compile: field {i} of {type} is missing from its `Flat` instance"
      tuplePath w steps
    return mkAppN (mkConst ctor.name type.getAppFn.constLevels!) (type.getAppArgs ++ fields.toArray)
  let u ← withLocalDeclD `v src fun v => do
    mkLambdaFVars #[v] (← ctorOf (match iβ with
      | some i => i.u.beta #[v]
      | none => v))
  let some i := iβ
    | return some (inverse u (fun x => rflEq (u.beta #[φ.beta #[x]]) x)
        (fun v => rflEq (φ.beta #[u.beta #[v]]) v))
  -- The tuple's laws, under the structure's constructor; the rest is structure eta and the
  -- unfolding of `Flat.flat`.
  let left (x : Lean.Expr) : MetaM Lean.Expr := do
    let fx := mkApp4 (mkConst ``LeanExe.Pipeline.Flat.flat) type β inst x
    let ctorFn ← withLocalDeclD `t β fun t => do mkLambdaFVars #[t] (← ctorOf t)
    let h ← transHint (← mkCongrArg ctorFn (← i.left fx)) (← rflEq (← ctorOf fx) x)
    mkExpectedTypeHint h (← mkEq (u.beta #[φ.beta #[x]]) x)
  let right (v : Lean.Expr) : MetaM Lean.Expr := do
    mkExpectedTypeHint (← i.right v) (← mkEq (φ.beta #[u.beta #[v]]) v)
  return some (inverse u left right)

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
      let callee : Callee := { name := name, sig := selfSig modes, denoteEq := base ++ `meaning_eq }
      let ctx : Ctx :=
        { base := base.getPrefix, sigs := sigs', funs := funs', callees := callee :: callees,
          vars := vars, env := env }
      let r ← reflect.reflectSplit ctx params.toList rhs
      return (r.src, r.proof)
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

/-- The list of the addresses and names of the tables `idxs` among the program's tables `tables`,
named `tableNames`, which a wrapper's theorems state. -/
def tableEntries (tables : Name) (tableNames : Array Name) (idxs : List Nat) :
    MetaM Lean.Expr := do
  let entryTy ← mkAppM ``Prod #[mkConst ``UInt64,
    mkApp (mkConst ``Array [.zero]) (mkConst ``UInt64)]
  let entries ← idxs.mapM fun i => do
    let addr ← kernelWhnf (← mkAppM ``UInt64.toNat
      #[← mkAppM ``tableAddr #[mkConst tables, mkNatLit i]])
    let some a := natOf addr
      | throwError "verified_compile: cannot evaluate the address of table {i}"
    mkAppM ``Prod.mk #[toExpr (UInt64.ofNat a), mkConst tableNames[i]!]
  return listExpr entryTy entries

/-- The definition of `r` as a function of the tuple of its arguments. -/
def leanFun (r : Reflected) : MetaM Lean.Expr :=
  withLocalDeclD `x r.argsType fun x => do
    let projs ← argProjsE x (paramModes r.params r.modes) r.params.length
    mkLambdaFVars #[x] (mkAppN (mkConst r.name) projs.toArray)

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
  let #[α, γ, ia, ic, aborts, m, entry, f, pre, post] := hTy.getAppArgs
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
    #[α, β, γ, δ, ia, ← userInst β, ic, ← userInst δ, aborts, m, entry, f, pre, post, h,
      r.flatArgs, r.flatResult, F, hF, mkConst argsAgree, mkConst resultAgree]

/-- `implementsProof` for a wrapper, whose theorem `h` is `ImplementsTables`. -/
def wrapperProof (funs : Name) (funsVal h F : Lean.Expr) (r : Reflected)
    (argsAgree resultAgree : Name) : MetaM Lean.Expr := do
  let hTy ← inferType h
  let #[α, γ, ia, ic, aborts, m, entry, f, tables, pre, post] := hTy.getAppArgs
    | throwError "verified_compile: the wrapper's theorem {hTy}"
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
    -- The callee, a projection of the wrapper's record.
    let chain ← getChain funsVal (← whnf fv) env
    let some (_, _, b) := (← inferType chain).eq?
      | throwError "verified_compile: the meaning of {get}"
    let c := mkApp r.flatResult (mkApp F y)
    let projs ← argProjsE y modes r.params.length
    let eq ← mkExpectedTypeHint (mkAppN (mkConst r.meaningEq) projs.toArray) (← mkEq b c)
    mkLambdaFVars #[y] (← transHint (← transHint step chain) eq)
  return mkAppN (mkConst ``ImplementsTables.transferAgree)
    #[α, β, γ, δ, ia, ← userInst β, ic, ← userInst δ, aborts, m, entry, f, tables, pre, post,
      h, r.flatArgs, r.flatResult, F, hF, mkConst argsAgree, mkConst resultAgree]

/-- The callee and the tables of a wrapper definition `fun params => g T₁ … Tₖ params`: `g` is a
listed definition and each `Tᵢ` a constant of type `Array UInt64`, which `g` takes as borrowed
arrays of words before the definition's own parameters. -/
def wrapperShape? (name : Name) (callees : List Callee) : MetaM (Option (Callee × List Name)) := do
  let info ← getConstInfoDefn name
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let .const fn _ := body.getAppFn | return none
    let some callee := callees.find? (·.name == fn) | return none
    let args := body.getAppArgs
    unless params.size < args.size do return none
    let k := args.size - params.size
    unless args.extract k args.size == params do return none
    let words := mkApp (mkConst ``Array [.zero]) (mkConst ``UInt64)
    let mut tables := #[]
    for t in args.extract 0 k do
      let .const c _ := t | return none
      unless ← isDefEq (← inferType t) words do return none
      tables := tables.push c
    unless callee.sig.params.take k == List.replicate k (.array .word) &&
        (callee.sig.modes.take k).all (· == .borrowed) do
      throwError "verified_compile: {fn} must take the tables of {name} as borrowed arrays of \
        words before its other parameters"
    return some (callee, tables.toList)

/-- Reflects the wrapper definition `name`, which applies `callee` to the tables `tables` and its
own parameters, and adds `base.denote_eq`: the callee's meaning at the tables and the parameters
is the flattening of `name` at the parameters, from the callee's own equation. -/
def reflectWrapper (base name : Name) (callee : Callee) (tables : List Name) :
    MetaM Reflected := do
  let info ← getConstInfoDefn name
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let types ← params.toList.mapM fun p => do tyOf (← inferType p)
    let resultShape ← shapeOf (← inferType body)
    let calleeEq := mkAppN (Lean.mkConst callee.denoteEq)
      (tables.toArray.map Lean.mkConst ++ params)
    let some (_, lhs, _) := (← inferType calleeEq).eq?
      | throwError "verified_compile: the equation of {callee.name}"
    let eq ← mkEq lhs (resultShape.apply (mkAppN (mkConst name) params))
    addTheorem (base ++ `denote_eq) (← mkForallFVars params eq)
      (← mkLambdaFVars params (← mkExpectedTypeHint calleeEq eq))
    let k := tables.length
    finishReflected base name params types resultShape.ty (← inferType body) callee.sig.aborts
      (callee.sig.modes.drop k) callee.sig.depth (base ++ `denote_eq)

/-- Adds `base.bound_eq` for the wrapper `name` of `callee`, whose bound is `boundName`: the
wrapper's bound at its arguments is the callee's bound at the tables and the arguments, or the
numeral that the callee's own equation states.  The proof is the chain of `Prog.bounds` from the
callee's index, which the kernel checks against the wrapper's bound by unfolding `Wrapper.bound`
and comparing the callee's index and environments. -/
def wrapperBoundEquation (base name boundName : Name) (callee : Callee)
    (progVal funsVal : Lean.Expr) : MetaM Unit := do
  let some cb := callee.bound? | return
  let info ← getConstInfoDefn name
  lambdaTelescope (← instantiateMVars info.value) fun params body => do
    let args := body.getAppArgs
    let k := args.size - params.size
    let owned (i : Nat) := callee.sig.mode i == .owned && !callee.sig.params[i]!.scalar
    let wTuple ← argsTuple
      (params.toList.zip ((List.range params.size).map fun i => owned (k + i)))
    let lhs := mkApp (mkConst boundName) wTuple
    let target := mkApp (mkConst cb.bound)
      (← argsTuple (args.toList.zip ((List.range args.size).map owned)))
    -- `Wrapper.bound tables w bounds env` unfolds to `bounds.get w.callee env'`.
    let some get ← unfoldDefinition? ((← getConstInfoDefn boundName).value.beta #[wTuple])
      | throwError "verified_compile: the bound of {name}"
    let #[_, _, _, fv, env] := get.headBeta.getAppArgs
      | throwError "verified_compile: the bound of {name}: {get}"
    let chain ← boundsChain progVal funsVal (← whnfR fv) env
    let some (_, _, chainRhs) := (← inferType chain).eq?
      | throwError "verified_compile: the bounds of {name}"
    checkBoundTarget m!"{name}" chainRhs target
    let h ← mkExpectedTypeHint chain (← mkEq lhs target)
    let (rhs, h) ← match cb.numeralEq with
      | some n => do
        let hn := mkAppN (mkConst n) args
        let some (_, _, c) := (← inferType hn).eq?
          | throwError "verified_compile: the bound equation of {callee.name}"
        pure (c, ← mkEqTrans h hn)
      | none => pure (target, h)
    addTheorem (base ++ `bound_eq) (← mkForallFVars params (← mkEq lhs rhs))
      (← mkLambdaFVars params h)

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
def fvarStx {m : Type → Type} [Monad m] [MonadQuotation m] : Nat → m Term
  | 0 => `(Verified.FVar.here)
  | k + 1 => do `(Verified.FVar.there $(← fvarStx k))

syntax (name := verifiedCompile) "verified_compile " ident " := " "[" ident,* "]" : command

/-- `verified_compile p := [f, g, …]` adds the program `p.program` of the listed definitions, in
order, each of which may call those before it and, when recursive, itself; the meanings
`p.funs` of its functions and the proof `p.meaning : Prog.Meaning p.program p.funs`; the module
`p.module`; the tables `p.tables` and the wrappers `p.wrappers`; for each definition `f`, the
theorem `p.f.implements` that the module computes `f`, at the function's index, at its exported
entry when its code takes the call depth, or, for a wrapper, at the wrapper's entry from a store
that holds the tables; `p.initial`, that the store in which the module starts meets the
allocator invariant and holds the tables; and `p.bytes`, the module's bytes with all the
functions' theorems. -/
@[command_elab verifiedCompile]
def elabVerifiedCompile : CommandElab
  | `(verified_compile $target := [$sources,*]) => do
    let names ← sources.getElems.mapM fun s => liftCoreM <| realizeGlobalConstNoOverloadWithInfo s
    let base := (← getCurrNamespace) ++ target.getId
    let (reflected, wraps, tableNames, funsVal) ← liftTermElabM do
      let mut sigs : List Sig := []
      let mut prog := Lean.mkConst ``Prog.nil
      let mut funs := Lean.mkConst ``Funs.nil
      let mut meaning := Lean.mkConst ``Prog.Meaning.nil
      let mut out : Array Reflected := #[]
      let mut callees : List Callee := []
      let mut wraps : Array (Reflected × Callee × List Nat) := #[]
      let mut tableNames : Array Name := #[]
      for name in names do
        let sigsExpr := listExpr (Lean.mkConst ``Sig) (sigs.map sigExpr)
        let fbase := base ++ Name.mkSimple name.getString!
        -- A wrapper passes constant tables to a listed function; it is no function of the
        -- program, and the module exports it after the entries.
        if let some (callee, tnames) ← wrapperShape? name callees then
          let mut idxs := #[]
          for t in tnames do
            match tableNames.findIdx? (· == t) with
            | some i => idxs := idxs.push i
            | none =>
              idxs := idxs.push tableNames.size
              tableNames := tableNames.push t
          wraps := wraps.push (← reflectWrapper fbase name callee tnames, callee, idxs.toList)
          continue
        let f := Lean.mkConst (fbase ++ `func)
        -- `getUnfoldEqnFor?` also returns the unfolding equation of a definition that is not
        -- recursive when an imported module has generated it, so recursion is tested first.
        let eqn? ← if ← isRecursiveDefinition name then getUnfoldEqnFor? name else pure none
        let r ← match eqn? with
          | none =>
            let r ← reflectDefinition fbase name sigsExpr funs prog callees
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
        callees := { name := name, sig := sig, denoteEq := r.meaningEq, bound? := r.bound? } ::
          callees
        out := out.push r
      let sigsExpr := listExpr (Lean.mkConst ``Sig) (sigs.map sigExpr)
      addDefinition (base ++ `program) (mkApp (Lean.mkConst ``Prog) sigsExpr) prog
      addDefinition (base ++ `funs) (mkApp (Lean.mkConst ``Funs) sigsExpr) funs
      addTheorem (base ++ `meaning)
        (mkApp3 (Lean.mkConst ``Prog.Meaning) sigsExpr (Lean.mkConst (base ++ `program))
          (Lean.mkConst (base ++ `funs))) meaning
      -- The tables, in the order of their first use, and the wrappers.
      let words := mkApp (Lean.mkConst ``Array [.zero]) (Lean.mkConst ``UInt64)
      addDefinition (base ++ `tables) (mkApp (Lean.mkConst ``List [.zero]) words)
        (listExpr words (tableNames.toList.map Lean.mkConst))
      let T := mkApp2 (Lean.mkConst ``List.length [.zero]) words
        (Lean.mkConst (base ++ `tables))
      let mut wexprs : Array Lean.Expr := #[]
      for (r, callee, idxs) in wraps do
        let some pos := out.findIdx? (·.name == callee.name)
          | throwError "verified_compile: the callee {callee.name}"
        let fvarTy := mkApp2 (Lean.mkConst ``FVar) sigsExpr (sigExpr callee.sig)
        let fvar ← Term.elabTermEnsuringType (← fvarStx (out.size - 1 - pos)) (some fvarTy)
        Term.synthesizeSyntheticMVarsNoPostponing
        let fvar ← instantiateMVars fvar
        let fins ← idxs.mapM fun i => do
          mkAppM ``Fin.mk #[mkNatLit i, ← mkDecideProof (← mkLt (mkNatLit i) T)]
        wexprs := wexprs.push (mkAppN (Lean.mkConst ``Wrapper.mk)
          #[sigsExpr, T, toExpr r.name.getString!, listExpr (mkApp (Lean.mkConst ``Fin) T) fins,
            ctxExpr r.params, tyExpr r.result, toExpr callee.sig.aborts,
            modesExpr callee.sig.modes, toExpr callee.sig.depth, fvar, ← mkEqRefl (toExpr true)])
      let wrapperTy := mkApp2 (Lean.mkConst ``Wrapper) sigsExpr T
      addDefinition (base ++ `wrappers) (mkApp (Lean.mkConst ``List [.zero]) wrapperTy)
        (listExpr wrapperTy wexprs.toList)
      addDefinition (base ++ `module) (Lean.mkConst ``Wasm.Module)
        (mkAppN (Lean.mkConst ``compileWith) #[sigsExpr, Lean.mkConst (base ++ `program),
          Lean.mkConst (base ++ `tables), Lean.mkConst (base ++ `wrappers)])
      return (out, wraps, tableNames, funs)
    -- The store in which the module starts.
    let initialProof ← `(Verified.compileWith_initialStore $(mkIdent (base ++ `program))
      $(mkIdent (base ++ `tables)) $(mkIdent (base ++ `wrappers)) (by decide +kernel))
    elabCommand (← `(theorem $(mkIdent (target.getId ++ `initial)) : type_of% $initialProof :=
      $initialProof))
    let progId := mkIdent (base ++ `program)
    let funsId := mkIdent (base ++ `funs)
    let meaningId := mkIdent (base ++ `meaning)
    let moduleId := mkIdent (base ++ `module)
    let tablesId := mkIdent (base ++ `tables)
    let wrappersId := mkIdent (base ++ `wrappers)
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
          pure (← `(Verified.Prog.correct_entryWith $progId $funsId $meaningId $tablesId
            $wrappersId $fvar rfl (j := $(Lean.quote j)) (by decide +kernel)), 2 + n + j)
        else
          pure (← `(Verified.ImplementsB.implementsA ((Verified.Prog.correctWith $progId $funsId
            $meaningId $tablesId $wrappersId $fvar).1 rfl)), 2 + k)
      -- The theorem for the flattened types, carried to Lean's types: each argument is
      -- represented as its flattening is, and the flattening of the result represents it.
      liftTermElabM do
        let h ← Term.elabTerm (← `(Verified.ImplementsA.lean $hStx)) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let h ← instantiateMVars h
        let F ← leanFun r
        let proof ← implementsProof (base ++ `funs) funsVal h F r (base ++ simple ++ `argsAgree)
          (base ++ simple ++ `resultAgree)
        -- The statement with the trap flag, the module, and the index as constants, and the
        -- precondition and postcondition beta-reduced.
        let ty ← inferType proof
        let args := ty.getAppArgs
        let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr r.aborts)
          |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit index)
          |>.set! 8 (← Core.betaReduce args[8]!) |>.set! 9 (← Core.betaReduce args[9]!))
        addTheorem implName claim proof
      claims := claims.push (← `(type_of% $(mkIdent implName)))
      proofs := proofs.push (mkIdent implName)
      -- For a function whose code takes no call depth, its allocation bound on Lean's argument
      -- tuple, and the theorem without a trap: under the condition that the bound fits when the
      -- function may trap, and with the growth of `top` bounded by the bound.
      unless r.depth do
        let boundName := base ++ simple ++ `bound
        liftTermElabM do
          let h0 ← Term.elabTerm (← `((Verified.Prog.correctWith $progId $funsId $meaningId
            $tablesId $wrappersId $fvar).1 rfl)) none
          Term.synthesizeSyntheticMVarsNoPostponing
          let h0 ← instantiateMVars h0
          let h0Ty ← instantiateMVars (← inferType h0)
          let #[_, _, _, _, _, _, _, _, boundEnv] := h0Ty.getAppArgs
            | throwError "verified_compile: the bounded theorem {h0Ty}"
          -- The program's bound of the function is the function's own bound, `Func.bound` among
          -- the functions before it, by the chain of `Prog.bounds`.  The theorem states it so,
          -- and `p.f.bound` unfolds to it, so the kernel never compares `Func.bound` with
          -- `Bounds.get`, which would unfold the compiler's bound.
          let progVal := (← getConstInfoDefn (base ++ `program)).value
          let fv := boundEnv.appArg!
          let .forallE _ envTy _ _ ← inferType boundEnv
            | throwError "verified_compile: the bound {boundEnv}"
          let hfun ← withLocalDeclD `env envTy fun env => do
            let chain ← boundsChain progVal funsVal fv env
            let some (_, _, own) := (← inferType chain).eq?
              | throwError "verified_compile: the bounds of {r.name}"
            mkLambdaFVars #[env] (← mkExpectedTypeHint chain (← mkEq (mkApp boundEnv env) own))
          let hfun ← mkAppM ``funext #[hfun]
          let some (_, _, ownFn) := (← inferType hfun).eq?
            | throwError "verified_compile: the bounds of {r.name}"
          let motive ← withLocalDeclD `B (← inferType boundEnv) fun B => do
            mkLambdaFVars #[B] (mkAppN h0Ty.getAppFn (h0Ty.getAppArgs.set! 8 B))
          let h0 ← mkAppM ``Eq.mp #[← mkCongrArg motive hfun, h0]
          let h0 ← mkExpectedTypeHint h0 (mkAppN h0Ty.getAppFn (h0Ty.getAppArgs.set! 8 ownFn))
          let h ← mkAppM ``ImplementsA.lean
            #[← mkAppM (if r.aborts then ``ImplementsB.trapFree else ``ImplementsB.noTrap) #[h0]]
          let proof ← implementsProof (base ++ `funs) funsVal h (← leanFun r) r
            (base ++ simple ++ `argsAgree) (base ++ simple ++ `resultAgree)
          let ty ← inferType proof
          let args := ty.getAppArgs
          let boundId := mkIdent boundName
          let pre ← if r.aborts then
              Term.elabTermEnsuringType (← `(fun x heap store =>
                LeanExe.Pipeline.Heap.Within heap store $moduleId ($boundId x)))
                (← inferType args[8]!)
            else Core.betaReduce args[8]!
          let post ← Term.elabTermEnsuringType (← `(fun x heap _ heap' _ =>
            heap'.top.toNat ≤ heap.top.toNat + $boundId x)) (← inferType args[9]!)
          Term.synthesizeSyntheticMVarsNoPostponing
          let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr false)
            |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit index)
            |>.set! 8 (← instantiateMVars pre) |>.set! 9 (← instantiateMVars post))
          addTheorem (base ++ simple ++ `trapFree) claim proof
    -- The wrappers' theorems, at their positions after the entries.
    let mut j := 0
    for (r, callee, idxs) in wraps do
      let simple := Name.mkSimple r.name.getString!
      let implName := base ++ simple ++ `implements
      let hStx ← `(Verified.Prog.correct_wrapper $progId $funsId $meaningId $tablesId $wrappersId
        (j := $(Lean.quote j)) rfl)
      liftTermElabM do
        let h ← Term.elabTerm (← `(Verified.ImplementsTables.lean $hStx)) none
        Term.synthesizeSyntheticMVarsNoPostponing
        let h ← instantiateMVars h
        let F ← leanFun r
        let proof ← wrapperProof (base ++ `funs) funsVal h F r (base ++ simple ++ `argsAgree)
          (base ++ simple ++ `resultAgree)
        -- The statement with the trap flag, the module, the index, and the tables' addresses
        -- and names as constants.
        let ty ← inferType proof
        let args := ty.getAppArgs
        let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr (r.aborts || r.depth))
          |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit (2 + n + entries + j))
          |>.set! 8 (← tableEntries (base ++ `tables) tableNames idxs)
          |>.set! 9 (← Core.betaReduce args[9]!) |>.set! 10 (← Core.betaReduce args[10]!))
        addTheorem implName claim proof
      claims := claims.push (← `(type_of% $(mkIdent implName)))
      proofs := proofs.push (mkIdent implName)
      -- For a wrapper whose callee's code takes no call depth, its bound and its theorem without
      -- a trap, as for a function.
      unless r.depth do
        let boundName := base ++ simple ++ `bound
        liftTermElabM do
          let h0Stx ← if r.aborts then
              `(Verified.Prog.wrapper_trapFree $progId $funsId $meaningId $tablesId $wrappersId
                (j := $(Lean.quote j)) rfl rfl)
            else
              `(Verified.Prog.wrapper_noTrap $progId $funsId $meaningId $tablesId $wrappersId
                (j := $(Lean.quote j)) rfl rfl rfl)
          let h0 ← Term.elabTerm h0Stx none
          Term.synthesizeSyntheticMVarsNoPostponing
          let h0 ← instantiateMVars h0
          let h0Ty ← instantiateMVars (← inferType h0)
          let #[_, _, ia, _, _, _, _, _, _, _, post] := h0Ty.getAppArgs
            | throwError "verified_compile: the wrapper's bounded theorem {h0Ty}"
          let #[ps, ms] := ia.getAppArgs
            | throwError "verified_compile: the instance {ia}"
          -- The wrapper's bound on the source arguments, `Wrapper.bound` in the postcondition.
          let boundEnv ← lambdaTelescope post fun xs body => do
            let some (_, _, rhs) := body.le?
              | throwError "verified_compile: the wrapper's postcondition {body}"
            mkLambdaFVars #[xs[0]!] rhs.appArg!
          let boundVal ← withLocalDeclD `x r.argsType fun x =>
            mkLambdaFVars #[x] (mkApp boundEnv
              (mkAppN (mkConst ``Env.ofArgs) #[ps, ms, (mkApp r.flatArgs x).headBeta])).headBeta
          addAndCompile <| .defnDecl <| mkDefinitionValEx boundName []
            (← mkArrow r.argsType (mkConst ``Nat)) boundVal
            (.regular (getMaxHeight (← getEnv) boundVal + 1)) .safe [boundName]
          wrapperBoundEquation (base ++ simple) r.name boundName callee
            (← getConstInfoDefn (base ++ `program)).value funsVal
          let h ← mkAppM ``ImplementsTables.lean #[h0]
          let proof ← wrapperProof (base ++ `funs) funsVal h (← leanFun r) r
            (base ++ simple ++ `argsAgree) (base ++ simple ++ `resultAgree)
          let ty ← inferType proof
          let args := ty.getAppArgs
          let boundId := mkIdent boundName
          let pre ← if r.aborts then
              Term.elabTermEnsuringType (← `(fun x heap store =>
                LeanExe.Pipeline.Heap.Within heap store $moduleId ($boundId x)))
                (← inferType args[9]!)
            else Core.betaReduce args[9]!
          let post ← Term.elabTermEnsuringType (← `(fun x heap _ heap' _ =>
            heap'.top.toNat ≤ heap.top.toNat + $boundId x)) (← inferType args[10]!)
          Term.synthesizeSyntheticMVarsNoPostponing
          let claim := mkAppN ty.getAppFn (args.set! 4 (toExpr false)
            |>.set! 5 (mkConst (base ++ `module)) |>.set! 6 (mkNatLit (2 + n + entries + j))
            |>.set! 8 (← tableEntries (base ++ `tables) tableNames idxs)
            |>.set! 9 (← instantiateMVars pre) |>.set! 10 (← instantiateMVars post))
          addTheorem (base ++ simple ++ `trapFree) claim proof
      j := j + 1
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
