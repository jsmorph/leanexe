import Verified.Reflect.BoundLemmas
import Lean

/-! The meta functions that build the equation between a source expression's allocation bound and
a Lean term from the lemmas of `Verified.Reflect.BoundLemmas`.  A builder takes the modes and the
live set at its site and returns the bound term with its proof.  Each lemma is applied with its
arguments named, and the others are found by unification at reducible transparency, so that two
terms that do not match fail at once: the kernel would otherwise unfold the compiler's bound to
compare them.  A side condition is a closed term, which the kernel evaluates to a constructor, and
its proof is `rfl`. -/

namespace Verified.Reflect

open Lean Meta

/-- A bound term and the proof that a source expression's `Expr.allocs` equals it. -/
structure Bound where
  cost : Lean.Expr
  proof : Lean.Expr

/-- From the modes and the live set at a site, as terms, the bound of a source expression, or
`none` for a form without bound lemmas. -/
abbrev BoundBuilder := Lean.Expr → Lean.Expr → MetaM (Option Bound)

def noBound : BoundBuilder := fun _ _ => return none

/-- The numeral `0 : Nat`. -/
def natZero : Lean.Expr := mkNatLit 0

def isNatZero (e : Lean.Expr) : Bool := e.nat? == some 0 || e.rawNatLit? == some 0

/-- The names of the binders of a `∀` type. -/
def binderNames : Lean.Expr → List Name
  | .forallE n _ b _ => n :: binderNames b
  | _ => []

/-- The lemma `n` applied to the arguments that `args` names, with the others found by unification
at reducible transparency.  Every argument must be found. -/
def appNamed (n : Name) (args : List (Name × Lean.Expr)) : MetaM Lean.Expr := do
  let c ← mkConstWithFreshMVarLevels n
  let ty ← inferType c
  let names := binderNames ty
  let (mvars, _, _) ← forallMetaTelescope ty
  for (name, v) in args do
    let some i := names.idxOf? name
      | throwError "verified_compile: {n} has no argument {name}"
    unless ← withReducible (isDefEq mvars[i]! v) do
      throwError "verified_compile: in {n}, the argument {name} does not match:{indentExpr v}\n\
        has type{indentExpr (← inferType v)}\nexpected{indentExpr (← inferType mvars[i]!)}"
  let app ← instantiateMVars (mkAppN c mvars)
  if app.hasExprMVar then
    let missing := (names.zip mvars.toList).filterMap fun (name, m) =>
      if m.isMVar then some name else none
    throwError "verified_compile: in {n}, the arguments {missing} are not determined"
  return app

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

/-- The modes and the live set of the `Expr.allocs` on the left of the equation that argument
`name` states. -/
def LemmaApp.allocsArgs (a : LemmaApp) (name : Name) : MetaM (Lean.Expr × Lean.Expr) := do
  let ty ← a.hypType name
  let some (_, lhs, _) := ty.eq?
    | throwError "verified_compile: the argument {name} of {a.name} is not an equation:{indentExpr ty}"
  let lhs := lhs.consumeMData
  -- `@Expr.allocs S funs bounds modes live Γ t e env`, possibly inside an addition.
  let lhs := match lhs.getAppFnArgs with
    | (``HAdd.hAdd, #[_, _, _, _, x, _]) => x
    | _ => lhs
  let (``Expr.allocs, #[_, _, _, modes, live, _, _, _, _]) := lhs.getAppFnArgs
    | throwError "verified_compile: the argument {name} of {a.name} is not a bound:{indentExpr lhs}"
  return (modes, live)

/-- The application, with every argument assigned. -/
def LemmaApp.finish (a : LemmaApp) : MetaM Lean.Expr := do
  let app ← instantiateMVars (mkAppN a.fn a.mvars)
  if app.hasExprMVar then
    let mut missing := #[]
    for (name, m) in a.names.zip a.mvars.toList do
      if (← instantiateMVars m).hasExprMVar then missing := missing.push name
    throwError "verified_compile: in {a.name}, the arguments {missing} are not determined"
  return app

/-- Runs the builder `b` of the part that argument `name` bounds, at the modes and live set that
the argument states, and assigns its proof. -/
def LemmaApp.child (a : LemmaApp) (name : Name) (b : BoundBuilder) : MetaM (Option Bound) := do
  let (modes, live) ← a.allocsArgs name
  let some r ← b modes live | return none
  a.assign name r.proof
  return some r

/-- The left and right sides of the equation that `p` proves. -/
def eqSides (p : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let some (_, l, r) := (← instantiateMVars (← inferType p)).eq?
    | throwError "verified_compile: the equation {p}"
  return (l, r)

/-- From `p : X = a + b`, the proof of `X = c` for `c` the sum without a summand `0`. -/
def dropZeroAdd (p : Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  let (_, rhs) ← eqSides p
  let (``HAdd.hAdd, #[_, _, _, _, a, b]) := rhs.getAppFnArgs | return (rhs, p)
  if isNatZero a && isNatZero b then return (natZero, ← mkEqTrans p (← mkAppM ``Nat.add_zero #[a]))
  if isNatZero a then return (b, ← mkEqTrans p (← mkAppM ``Nat.zero_add #[b]))
  if isNatZero b then return (a, ← mkEqTrans p (← mkAppM ``Nat.add_zero #[a]))
  return (rhs, p)

/-- The sum `((x₀ + x₁) + …) + xₙ` of `xs` without its summands `0`, and the proof that the sum
equals it. -/
def sumNorm (xs : List Lean.Expr) : MetaM (Lean.Expr × Lean.Expr) := do
  match xs with
  | [] => return (natZero, ← mkEqRefl natZero)
  | x :: rest =>
    let mut acc := x
    let mut proof ← mkEqRefl x
    let mut sum := x
    for y in rest do
      -- `sum + y = acc + y`, then the sum without a zero.
      sum ← mkAppM ``HAdd.hAdd #[sum, y]
      let step ← mkCongrArg (← withLocalDeclD `z (mkConst ``Nat) fun z => do
        mkLambdaFVars #[z] (← mkAppM ``HAdd.hAdd #[z, y])) proof
      let (c, p) ← dropZeroAdd (← mkEqTrans step (← mkEqRefl (← mkAppM ``HAdd.hAdd #[acc, y])))
      acc := c
      proof := p
    return (acc, proof)

/-- From `p : X = s` for a left-nested sum `s` of the terms `xs`, the proof of `X = c` for `c` the
sum without its summands `0`. -/
def normSum (p : Lean.Expr) (xs : List Lean.Expr) : MetaM Bound := do
  let (c, h) ← sumNorm xs
  return ⟨c, ← mkEqTrans p h⟩

/-- The value that the kernel computes for the closed term `e`: a constructor or a literal. -/
def kernelEval (e : Lean.Expr) : MetaM Lean.Expr := do
  match Kernel.whnf (← getEnv) (← getLCtx) e with
  | .ok r => return r
  | .error ex => throwKernelException ex

/-- The proof of `e = v` by `rfl` for the closed term `e` and the constructor `v` it evaluates to. -/
def evalEq (e v : Lean.Expr) : MetaM Lean.Expr := do
  mkExpectedTypeHint (← mkEqRefl v) (← mkEq e v)

/-- The Boolean that the closed term `e` evaluates to, with an error that names `what` when it does
not evaluate to `true` or `false`. -/
def evalBool (what : MessageData) (e : Lean.Expr) : MetaM Bool := do
  let v ← kernelEval e
  if v.isConstOf ``Bool.true then return true
  if v.isConstOf ``Bool.false then return false
  throwError "verified_compile: {what} does not evaluate to a Boolean:{indentExpr v}"

/-- Whether the closed `Mode` term `e` evaluates to `Mode.owned`, with an error that names `what`
when it evaluates to neither mode. -/
def evalOwned (what : MessageData) (e : Lean.Expr) : MetaM Bool := do
  let v ← kernelEval e
  if v.isConstOf ``Mode.owned then return true
  if v.isConstOf ``Mode.borrowed then return false
  throwError "verified_compile: {what} does not evaluate to a mode:{indentExpr v}"

def modeConst (owned : Bool) : Lean.Expr :=
  mkConst (if owned then ``Mode.owned else ``Mode.borrowed)

def boolConst (b : Bool) : Lean.Expr := mkConst (if b then ``Bool.true else ``Bool.false)

end Verified.Reflect
