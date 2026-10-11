import Verified.Reflect.FitsLemmas
import Lean

/-! The meta functions that build the equation between a source expression's allocation bound and
a Lean term from the lemmas of `Verified.Reflect.BoundLemmas`.  A builder takes the modes and the
live set at its site and returns the bound term with its proof.  Each lemma is applied with its
arguments named, and the others are found by unification at reducible transparency, so that two
terms that do not match fail at once: the kernel would otherwise unfold the compiler's bound to
compare them.  A side condition is a closed term, which the kernel evaluates to a constructor, and
its proof is `rfl`.

Each lemma's conclusion is built from its arguments, and each congruence is stated with its sides,
so the type that `inferType` computes for a proof is the one the kernel infers, and two equations
join where their terms are identical.  The kernel compares two closed `Nat` sums that differ by
evaluating both, so the hints that do compare different terms compare them where one holds a free
variable, or under heads that the kernel unfolds by their heights before it compares arguments. -/

namespace Verified.Reflect

open Lean Meta

/-- A term and the proof that a source expression's bound, `Expr.allocs`, or its frames condition,
`Expr.fits`, equals it. -/
structure Bound where
  term : Lean.Expr
  proof : Lean.Expr
  deriving Inhabited

/-- From the modes, the paid flags, and the live set at a site, as terms, the bound of a source
expression. -/
abbrev BoundBuilder := Lean.Expr → Lean.Expr → Lean.Expr → MetaM Bound

/-- The frames condition of a source expression. -/
abbrev FitsBuilder := MetaM Bound

/-- The numeral `0 : Nat`. -/
def natZero : Lean.Expr := mkNatLit 0

/-- Whether `e` is the numeral `0` in the form of the lemma statements, so that a lemma about `0`
applies to it syntactically. -/
def isNatZero (e : Lean.Expr) : Bool := e == natZero

/-- `HAdd.hAdd` on `Nat` with the instance of the lemma statements. -/
def natAdd : Lean.Expr :=
  let nat := mkConst ``Nat
  mkApp4 (mkConst ``HAdd.hAdd [0, 0, 0]) nat nat nat
    (mkApp2 (mkConst ``instHAdd [0]) nat (mkConst ``instAddNat))

/-- `HMul.hMul` on `Nat` with the instance of the lemma statements. -/
def natMul : Lean.Expr :=
  let nat := mkConst ``Nat
  mkApp4 (mkConst ``HMul.hMul [0, 0, 0]) nat nat nat
    (mkApp2 (mkConst ``instHMul [0]) nat (mkConst ``instMulNat))

/-- The names of the binders of a `∀` type. -/
def binderNames : Lean.Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- A lemma being applied: its arguments are metavariables, which the builder assigns by name. -/
structure LemmaApp where
  name : Name
  fn : Lean.Expr
  names : List Name
  mvars : Array Lean.Expr

def LemmaApp.index (a : LemmaApp) (name : Name) : MetaM Nat := do
  let some i := a.names.idxOf? name
    | throwError "verified_compile: {a.name} has no argument {name}"
  return i

/-- Assigns argument `name` the value `v`, after checking at reducible transparency that the types
agree. -/
def LemmaApp.assign (a : LemmaApp) (name : Name) (v : Lean.Expr) : MetaM Unit := do
  let m := a.mvars[← a.index name]!
  let expected ← instantiateMVars (← inferType m)
  let actual ← inferType v
  unless ← withReducible (isDefEq expected actual) do
    throwError "verified_compile: in {a.name}, the argument {name} has type{indentExpr actual}\n\
      but {a.name} expects{indentExpr (← instantiateMVars expected)}"
  unless ← withReducible (isDefEq m v) do
    throwError "verified_compile: in {a.name}, cannot assign the argument {name}"

/-- The lemma `n` with the arguments that `args` names assigned; names that `n` does not take are
ignored, since the builders pass the same context to every lemma. -/
def LemmaApp.start (n : Name) (args : List (Name × Lean.Expr)) : MetaM LemmaApp := do
  let fn ← mkConstWithFreshMVarLevels n
  let ty ← inferType fn
  let (mvars, _, _) ← forallMetaTelescope ty
  let a : LemmaApp := ⟨n, fn, binderNames ty, mvars⟩
  for (name, v) in args do
    if a.names.contains name then a.assign name v
  return a

/-- The type of argument `name`, with the assigned arguments substituted. -/
def LemmaApp.hypType (a : LemmaApp) (name : Name) : MetaM Lean.Expr := do
  instantiateMVars (← inferType a.mvars[← a.index name]!)

/-- The modes, the paid flags, and the live set of the `Expr.allocs` on the left of the equation
that argument `name` states. -/
def LemmaApp.allocsArgs (a : LemmaApp) (name : Name) :
    MetaM (Lean.Expr × Lean.Expr × Lean.Expr) := do
  let ty ← a.hypType name
  let some (_, lhs, _) := ty.eq?
    | throwError "verified_compile: the argument {name} of {a.name} is not an equation:{indentExpr ty}"
  let (``Expr.allocs, #[_, _, _, modes, paid, live, _, _, _, _]) := lhs.consumeMData.getAppFnArgs
    | throwError "verified_compile: the argument {name} of {a.name} is not a bound:{indentExpr lhs}"
  return (modes, paid, live)

/-- The application, with every argument assigned. -/
def LemmaApp.finish (a : LemmaApp) : MetaM Lean.Expr := do
  let app ← instantiateMVars (mkAppN a.fn a.mvars)
  if app.hasExprMVar then
    let mut missing := #[]
    for (name, m) in a.names.zip a.mvars.toList do
      if (← instantiateMVars m).hasExprMVar then missing := missing.push name
    throwError "verified_compile: in {a.name}, the arguments {missing} are not determined"
  return app

/-- Runs the builder `b` of the part that argument `name` bounds, at the modes, paid flags, and live
set that the argument states, and assigns its proof. -/
def LemmaApp.child (a : LemmaApp) (name : Name) (b : BoundBuilder) : MetaM Bound := do
  let (modes, paid, live) ← a.allocsArgs name
  let r ← b modes paid live
  a.assign name r.proof
  return r

/-- The left and right sides of the equation that `p` proves. -/
def eqSides (p : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let some (_, l, r) := (← instantiateMVars (← inferType p)).eq?
    | throwError "verified_compile: the equation {p}"
  return (l, r)

/-- `congrArg f h : f a = f b` for `h : a = b`, with the sides given. -/
def congrArgOn (f a b h : Lean.Expr) : MetaM Lean.Expr := do
  let α ← inferType a
  let β ← inferType (mkApp f a)
  return mkAppN (mkConst ``congrArg [← getLevel α, ← getLevel β]) #[α, β, a, b, f, h]

/-- `congr hf hx : f a = g b` for `hf : f = g` and `hx : a = b`, with the sides given. -/
def congrOn (f g a b hf hx : Lean.Expr) : MetaM Lean.Expr := do
  let α ← inferType a
  let β ← inferType (mkApp f a)
  return mkAppN (mkConst ``congr [← getLevel α, ← getLevel β]) #[α, β, f, g, a, b, hf, hx]

/-- `op a b = op a' b'` from `ha : a = a'` and `hb : b = b'`, either `none` for `rfl`, by
congruence with the sides given. -/
def congr2 (op a a' b b' : Lean.Expr) (ha? hb? : Option Lean.Expr) : MetaM Lean.Expr := do
  let ha ← match ha? with | some h => pure h | none => mkEqRefl a
  let hb ← match hb? with | some h => pure h | none => mkEqRefl b
  congrOn (mkApp op a) (mkApp op a') b b' (← congrArgOn op a a' ha) hb

/-- The weak head normal form of `e` by the kernel: a constructor or a literal for a closed term of
an inductive type.  The reflector evaluates the compiler's functions of a source body this way:
Meta's `reduce` would recurse once per level of the body and exceed the elaborator's recursion
limit on a deep one. -/
def kernelWhnf (e : Lean.Expr) : MetaM Lean.Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => return r
  | .error ex => throwKernelException ex

/-- The value of a numeral, raw or in the form `OfNat.ofNat`. -/
def natOf (n : Lean.Expr) : Option Nat := n.nat? <|> n.rawNatLit?

/-- The numeral, in the form of the lemma statements, that the closed `Nat` term `e` evaluates
to. -/
def evalNat (e : Lean.Expr) : MetaM Lean.Expr := do
  let v ← kernelWhnf e
  let some n := natOf v
    | throwError "verified_compile: {e} does not evaluate to a numeral:{indentExpr v}"
  return mkNatLit n

/-- The proof of `e = v` by `rfl` for the closed term `e` and the constructor `v` it evaluates to. -/
def evalEq (e v : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl v) (← mkEq e v)

/-- The Boolean that the closed term `e` evaluates to, with an error that names `what` when it does
not evaluate to `true` or `false`. -/
def evalBool (what : MessageData) (e : Lean.Expr) : MetaM Bool := do
  let v ← kernelWhnf e
  if v.isConstOf ``Bool.true then return true
  if v.isConstOf ``Bool.false then return false
  throwError "verified_compile: {what} does not evaluate to a Boolean:{indentExpr v}"

/-- Whether the closed `Mode` term `e` evaluates to `Mode.owned`, with an error that names `what`
when it evaluates to neither mode. -/
def evalOwned (what : MessageData) (e : Lean.Expr) : MetaM Bool := do
  let v ← kernelWhnf e
  if v.isConstOf ``Mode.owned then return true
  if v.isConstOf ``Mode.borrowed then return false
  throwError "verified_compile: {what} does not evaluate to a mode:{indentExpr v}"

def modeConst (owned : Bool) : Lean.Expr :=
  mkConst (if owned then ``Mode.owned else ``Mode.borrowed)

def boolConst (b : Bool) : Lean.Expr := mkConst (if b then ``Bool.true else ``Bool.false)

/-- For `x = a * 1`, with `1` in the form of the lemma statements, `a` and the proof of `x = a`. -/
def mulOne? (x : Lean.Expr) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  let (``HMul.hMul, #[_, _, _, _, a, w]) := x.getAppFnArgs | return none
  unless x.appFn!.appFn! == natMul && w == mkNatLit 1 do return none
  return some (a, ← mkAppM ``Nat.mul_one #[a])

end Verified.Reflect
