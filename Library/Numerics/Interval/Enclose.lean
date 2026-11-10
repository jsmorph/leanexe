import Library.Numerics.Interval.EncloseAttr
import Library.Numerics.Interval.FunctionsProof

/-!
One source for a real function and its interval program.

`enclosure_def f (x y) := body` reads `body`, a chain of `let` bindings over real expressions,
and declares three things: the real function `f`, the interval function `f.interval` in the
verified compiler's dialect, which takes the tables of `sin`, `cos`, and `pow` before its interval
parameters, and the theorem `f.encloses`, that the result of `f.interval` encloses the result of
`f` when each interval argument encloses the real argument.  A body may end in a tuple, and a
`let` may bind the components of a tuple.

The interval function evaluates each real operation with the interval operation of the table
below.  A call of another function `g` becomes a call of `g.interval`, whose theorem
`g.encloses` carries the label `enclose`.

| Real expression | Interval expression |
|---|---|
| `a + b`, `a - b`, `a * b`, `a / b`, `-a`, `\|a\|` | `add`, `sub`, `mul`, `div`, `neg`, `abs` |
| A natural number literal, a decimal literal | `ofInt`, `ratio` |
| `√a`, `sin a`, `cos a`, `max a b` | `sqrt`, `sinI`, `cosI`, `imax` |
| `a ^ (2 / 3 : ℝ)`, `a ^ (3 / 2 : ℝ)`, `a ^ (7 / 2 : ℝ)` | `twoThirds`, `threeHalves`, `sevenHalves` |
| `if a < b then p else q`, `if a > b then p else q` | `ifPos` on the difference |

The tactic `enclose` proves the theorem.  It walks the two chains of `let` bindings together,
proves for each pair of bound values that the interval value encloses the real value, by the
theorems labelled `enclose`, and continues with the two bound variables and that fact.
-/

namespace Library.Numerics.Interval

attribute [enclose] encloses_add encloses_sub encloses_mul encloses_div encloses_neg encloses_abs
  encloses_sqrt encloses_imax encloses_ifLt encloses_sinI encloses_cosI encloses_twoThirds
  encloses_threeHalves encloses_sevenHalves

namespace Enclose

open Lean Meta Elab Tactic

/-! ### The translation -/

def tableNames : Array Name := #[`trigInv, `trigHalf, `powLog, `powExp]

def tables : Array Ident := tableNames.map mkIdent

/-- Component `i` of the `k` components of the tuple `p`. -/
def component (p : Term) (i k : Nat) : MacroM Term := do
  let mut e := p
  for _ in [0:i] do
    e ← `(($e).2)
  if i + 1 < k then `(($e).1) else pure e

/-- The bindings of the components of a tuple, before `body`. -/
def bindComponents (p : Ident) (xs : Array Ident) (body : Term) : MacroM Term := do
  let mut b := body
  for i in [0:xs.size] do
    let j := xs.size - 1 - i
    let x := xs[j]!
    let v ← component p j xs.size
    b ← `(let $x:ident := $v; $b)
  pure b

/-- The real body: the source with each tuple binding written as bindings of components. -/
partial def realBody (stx : Term) : MacroM Term := do
  match stx with
  | `(let ($x:ident, $xs:ident,*) := $v; $b) =>
    let p := mkIdent `tuple
    let rest ← bindComponents p (#[x] ++ xs.getElems) (← realBody b)
    `(let $p:ident := $v; $rest)
  | `(let $x:ident := $v; $b) => do `(let $x:ident := $v; $(← realBody b))
  | _ => pure stx

/-- The interval body. -/
partial def intervalBody (stx : Term) : MacroM Term := do
  match stx with
  | `(($a)) => do `(($(← intervalBody a)))
  | `(let ($x:ident, $xs:ident,*) := $v; $b) =>
    let p := mkIdent `tuple
    let rest ← bindComponents p (#[x] ++ xs.getElems) (← intervalBody b)
    `(let $p:ident := $(← intervalBody v); $rest)
  | `(let $x:ident := $v; $b) => do
    `(let $x:ident := $(← intervalBody v); $(← intervalBody b))
  | `(($a, $as,*)) => do
    let a' ← intervalBody a
    let as' ← as.getElems.mapM intervalBody
    `(($a', $as',*))
  | `(if $a < $b then $p else $q) => do
    `(Library.Numerics.Interval.ifPos
      (Library.Numerics.Interval.sub $(← intervalBody b) $(← intervalBody a))
      $(← intervalBody p) $(← intervalBody q))
  | `(if $a > $b then $p else $q) => do
    `(Library.Numerics.Interval.ifPos
      (Library.Numerics.Interval.sub $(← intervalBody a) $(← intervalBody b))
      $(← intervalBody p) $(← intervalBody q))
  | `($a ^ (2 / 3 : ℝ)) => do
    `(Library.Numerics.Interval.twoThirds $(tables[2]!) $(tables[3]!) $(← intervalBody a))
  | `($a ^ (3 / 2 : ℝ)) => do `(Library.Numerics.Interval.threeHalves $(← intervalBody a))
  | `($a ^ (7 / 2 : ℝ)) => do `(Library.Numerics.Interval.sevenHalves $(← intervalBody a))
  | `($a + $b) => do
    `(Library.Numerics.Interval.add $(← intervalBody a) $(← intervalBody b))
  | `($a - $b) => do
    `(Library.Numerics.Interval.sub $(← intervalBody a) $(← intervalBody b))
  | `($a * $b) => do
    `(Library.Numerics.Interval.mul $(← intervalBody a) $(← intervalBody b))
  | `($a / $b) => do
    `(Library.Numerics.Interval.div $(← intervalBody a) $(← intervalBody b))
  | `(-$a) => do `(Library.Numerics.Interval.neg $(← intervalBody a))
  | `(|$a|) => do `(Library.Numerics.Interval.abs $(← intervalBody a))
  | `(√$a) => do `(Library.Numerics.Interval.sqrt $(← intervalBody a))
  | `($n:num) => `(Library.Numerics.Interval.ofInt $n)
  | `($x:scientific) =>
    match x.raw.isScientificLit? with
    | some (m, true, e) =>
      `(Library.Numerics.Interval.ratio $(Syntax.mkNumLit (toString m))
        $(Syntax.mkNumLit (toString (10 ^ e))))
    | some (m, false, e) =>
      `(Library.Numerics.Interval.ofInt $(Syntax.mkNumLit (toString (m * 10 ^ e))))
    | none => Macro.throwErrorAt stx "enclosure_def: unsupported literal"
  | `($f:ident $args*) => do
    let args' ← args.mapM intervalBody
    match f.getId with
    | `sin | `Real.sin =>
      `(Library.Numerics.Interval.sinI $(tables[0]!) $(tables[1]!) $args'*)
    | `cos | `Real.cos =>
      `(Library.Numerics.Interval.cosI $(tables[0]!) $(tables[1]!) $args'*)
    | `max => `(Library.Numerics.Interval.imax $args'*)
    | name =>
      let g := mkIdentFrom f (name ++ `interval)
      `($g $tables* $args'*)
  | `($_:ident) => pure stx
  | _ => Macro.throwErrorAt stx "enclosure_def: unsupported term"

/-- The number of components of the result of a body. -/
partial def resultSize (stx : Term) : Nat :=
  match stx with
  | `(let ($_:ident, $_:ident,*) := $_; $b) => resultSize b
  | `(let $_:ident := $_; $b) => resultSize b
  | `(($_, $as,*)) => as.getElems.size + 1
  | _ => 1

/-- The relation of the results: `Encloses`, or its product for a tuple. -/
def resultRelation : Nat → MacroM Term
  | 0 | 1 => `(Library.Numerics.Interval.Encloses)
  | k + 1 => do
    `(Library.Numerics.Interval.prodRel Library.Numerics.Interval.Encloses
      $(← resultRelation k))

/-! ### The tactic -/

/-- The relation between an interval value of type `ty` and its real value. -/
partial def relationOf (ty : Expr) : MetaM Expr := do
  let ty ← whnfR ty
  if ty.isConstOf ``Interval then return mkConst ``Encloses
  match ty.getAppFnArgs with
  | (``Prod, #[a, b]) => mkAppM ``prodRel #[← relationOf a, ← relationOf b]
  | _ => throwError "enclose: no relation for values of type {ty}"

/-- Runs a tactic on one goal and returns the goals it leaves. -/
def runOn (g : MVarId) (tac : TSyntax `tactic) : TacticM (List MVarId) := do
  let saved ← getGoals
  setGoals [g]
  evalTactic tac
  let rest ← getGoals
  setGoals saved
  return rest

/-- The value of an `Int64` literal. -/
def literal? (e : Expr) : Option Nat :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?
  | _ => none

/-- Splits a hypothesis that is a conjunction into its parts, repeatedly. -/
partial def split (g : MVarId) (h : FVarId) : MetaM MVarId := g.withContext do
  let ty ← whnfR (← instantiateMVars (← h.getType))
  if ty.isAppOfArity ``And 2 then
    let #[s] ← g.cases h | throwError "enclose: cannot split {ty}"
    let mut g' := s.mvarId
    for f in s.fields do
      g' ← split g' f.fvarId!
    return g'
  else return g

/-- Proves that an interval expression encloses a real expression. -/
partial def solve (rules : Array Name) (g : MVarId) : TacticM Unit := g.withContext do
  if ← withReducible g.assumptionCore then return
  let ty ← whnfR (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``Encloses 2 then
    match ty.appFn!.appArg!.getAppFnArgs with
    | (``ofInt, #[n]) =>
      let some m := literal? n | throwError "enclose: {n} is not a literal"
      let rest ← runOn g (← `(tactic| exact encloses_ofInt' (m := $(quote m))
        (by decide +kernel) (by decide +kernel) (by norm_num)))
      unless rest.isEmpty do throwError "enclose: the literal {n} does not match {ty}"
      return
    | (``ratio, #[n, d]) =>
      let some m := literal? n | throwError "enclose: {n} is not a literal"
      let some k := literal? d | throwError "enclose: {d} is not a literal"
      let rest ← runOn g (← `(tactic| exact encloses_ratio' (m := $(quote m)) (k := $(quote k))
        (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by norm_num)))
      unless rest.isEmpty do throwError "enclose: the literals {n} and {d} do not match {ty}"
      return
    | _ => pure ()
  for rule in rules do
    let r ← observing? (withReducible (g.apply (← mkConstWithFreshMVarLevels rule)))
    if let some gs := r then
      for g' in gs do
        unless ← g'.isAssigned do solve rules g'
      return
  if ty.isAppOfArity ``And 2 then
    for g' in ← g.constructor do
      solve rules g'
    return
  throwError "enclose: no rule proves {ty}"

/-- Walks two chains of `let` bindings together. -/
partial def chain (rules : Array Name) (g : MVarId) : TacticM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let args := ty.getAppArgs
  unless 2 ≤ args.size do throwError "enclose: the goal {ty} is not a relation of two values"
  let relation := mkAppN ty.getAppFn (args.extract 0 (args.size - 2))
  match args[args.size - 2]!.consumeMData, args[args.size - 1]!.consumeMData with
  | .letE n1 t1 v1 b1 _, .letE n2 t2 v2 b2 _ =>
    let rel ← relationOf t1
    let fact ← mkFreshExprMVar (mkApp2 rel v1 v2)
    solve rules fact.mvarId!
    let next ← withLocalDeclD n1 t1 fun x => withLocalDeclD (n2.appendAfter "'") t2 fun y =>
      withLocalDeclD (n1.appendBefore "h_") (mkApp2 rel x y) fun h =>
        mkForallFVars #[x, y, h] (mkApp2 relation (b1.instantiate1 x) (b2.instantiate1 y))
    let rest ← mkFreshExprMVar next
    g.assign (mkApp3 rest v1 v2 fact)
    let (fvars, g') ← rest.mvarId!.introNP 3
    chain rules (← split g' fvars[2]!)
  | _, _ => solve rules g

/-- Proves that an interval function made by `enclosure_def` encloses its real function. -/
elab "enclose" : tactic => do
  let mut g ← getMainGoal
  for h in (← g.getDecl).lctx do
    unless h.isImplementationDetail do
      g ← split g h.fvarId
  let rules ← labelled `enclose
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let args := ty.getAppArgs
    unless 2 ≤ args.size do throwError "enclose: the goal {ty} is not a relation of two values"
    let some i ← unfoldDefinition? args[args.size - 2]!
      | throwError "enclose: cannot unfold {args[args.size - 2]!}"
    let some r ← unfoldDefinition? args[args.size - 1]!
      | throwError "enclose: cannot unfold {args[args.size - 1]!}"
    let args := (args.set! (args.size - 2) i.headBeta).set! (args.size - 1) r.headBeta
    let g' ← g.replaceTargetDefEq (mkAppN ty.getAppFn args)
    chain rules g'
  replaceMainGoal []

/-! ### The command -/

syntax (name := enclosureDef) (docComment)? "enclosure_def " ident "(" ident* ")" " := " term :
  command

macro_rules
  | `($[$doc:docComment]? enclosure_def $name ($ps*) := $body) => do
    let iname := mkIdentFrom name (name.getId ++ `interval)
    let tname := mkIdentFrom name (name.getId ++ `encloses)
    let qs := ps.map fun p => mkIdentFrom p (p.getId.appendAfter "'")
    let hs := ps.map fun p => mkIdentFrom p (p.getId.appendBefore "h_")
    let rel ← resultRelation (resultSize body)
    let real ← `($[$doc:docComment]? noncomputable def $name ($ps* : ℝ) := $(← realBody body))
    let interval ← `(set_option linter.unusedVariables false in
      def $iname ($tables* : Array UInt64) ($ps* : Library.Numerics.Interval.Interval) :=
        $(← intervalBody body))
    let thm ← `(@[enclose] theorem $tname {powLog powExp : Array UInt64}
        {$ps* : Library.Numerics.Interval.Interval} {$qs* : ℝ}
        $[($hs : Library.Numerics.Interval.Encloses $ps $qs)]* :
        $rel ($iname Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi
          powLog powExp $ps*) ($name $qs*) := by enclose)
    return mkNullNode #[real, interval, thm]

end Enclose

end Library.Numerics.Interval
