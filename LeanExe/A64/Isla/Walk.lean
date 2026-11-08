import LeanExe.A64.Isla.Check
import LeanExe.A64.Isla.Profile

/-!
The walk of the traces of the load and store forms, which the theorems of `LDR`, `STR`, and
`STRB` in `tests/TestSupport/A64/Isla` share.  A trace of a memory form holds hundreds of events.
On a hypothesis or goal that holds the trace's literal, a step of `isla_fwd` or `isla_walk` costs
the size of the remaining trace, since `rw` and `simp` traverse it.  `isla_nodes F` gives each node
of the trace of `F` a definition that names the nodes below it, so that a path's hypothesis or goal
holds one event and the name of the rest, and a step costs the size of an event.  `isla_ctx F π`
evaluates the premise of `Agrees` on the registers outside the model once for each footprint.
`mem_fwd` takes a path's hypothesis through the trace, and `mem_bwd` builds the path to `exec`'s
state, giving each declared variable, through `mem_wit`, the value that the first event reading it
reads.

`run_congr` and `runSome_congr` keep `simp` out of the trace of a path and its variables, which a
walk extends with values that `simp` already evaluated.  A module that walks a trace declares them
`congr` locally: as global congruence lemmas they would act on every `simp` call of a module that
imports this one, and a call that unfolds a footprint inside a path, as the proofs of the register
forms do, would leave the path unchanged.  The address translation computes with masks that are
literals of the traces, and the lemmas on those literals reduce it to linear arithmetic for
`omega`.  `ttbr_facts` states the mask constraint of `tests/isla/traces.sh` on `TTBR0_NS`, a
multiple of 32 in the RAM GiB, and `desc_eq` and `desc0_eq` state the descriptors of
`LeanExe/A64/Table.lean` that the walk reads.
-/

namespace LeanExe.A64.Isla

/-- With `attribute [local congr]`, `simp` enters neither the trace of a path nor its variables,
which a walk extends with values that `simp` already evaluated. -/
theorem run_congr {P : Platform} {A : Abstract} {t : Trace} {ρ : Vars} {s s' : State}
    {σ σ' : Sys} {o o' : Outcome} (h2 : s = s') (h3 : σ = σ') (h4 : o = o') :
    Trace.Run P A t ρ s σ o = Trace.Run P A t ρ s' σ' o' := by
  subst h2 h3 h4
  rfl

theorem runSome_congr {P : Platform} {A : Abstract} {ts : List Trace} {ρ : Vars}
    {s s' : State} {σ σ' : Sys} {o o' : Outcome} (h2 : s = s') (h3 : σ = σ') (h4 : o = o') :
    Trace.RunSome P A ts ρ s σ o = Trace.RunSome P A ts ρ s' σ' o' := by
  subst h2 h3 h4
  rfl

open Lean in
/-- The value that the chain `ρ` of `Vars.set` on `fun _ => none` gives the variable `y`. -/
partial def lookupVars (ρ : Expr) (y : Nat) : Option Expr :=
  if ρ.isAppOfArity ``Vars.set 3 then
    match ρ.appFn!.appArg!.nat? with
    | some x =>
      if x == y then some (mkApp2 (mkConst ``Option.some [Level.zero]) (mkConst ``Val) ρ.appArg!)
      else lookupVars ρ.appFn!.appFn!.appArg! y
    | none => none
  else match ρ with
    | .lam _ _ b _ => if b.isAppOfArity ``Option.none 1 then some b else none
    | _ => none

open Lean Meta Simp in
/-- Reads a variable from a chain of `Vars.set` in one step, where `Vars.set_apply` takes a step
per link. -/
dsimproc_decl reduceVars (Vars.set _ _ _ _) := fun e => do
  unless e.isAppOfArity ``Vars.set 4 do return .continue
  let some y := e.appArg!.nat? | return .continue
  match lookupVars e.appFn! y with
  | some v => return .visit v
  | none => return .continue

open Lean Meta Simp in
/-- Evaluates `gpr` of a literal in one step, with the entry of `gprs`, where unfolding
`List.lookup` takes a step per register. -/
dsimproc_decl reduceGpr (gpr _) := fun e => do
  unless e.isAppOfArity ``gpr 1 do return .continue
  let .lit (.strVal r) := e.appArg! | return .continue
  let some v := (← getConstInfo ``gprs).value? | return .continue
  let some (_, ps) := (← instantiateMVars v).listLit? | return .continue
  let fin := mkApp (mkConst ``Fin) (mkNatLit 31)
  for p in ps do
    if p.isAppOfArity ``Prod.mk 4 then
      if let .lit (.strVal q) := p.appFn!.appArg! then
        if q == r then return .done (mkApp2 (mkConst ``Option.some [Level.zero]) fin p.appArg!)
  return .done (mkApp (mkConst ``Option.none [Level.zero]) fin)

open Lean in
/-- Adds a definition of each node of the trace `t` under the footprint `F`, numbered from the
counter, and returns the name of the definition of `t`. -/
partial def addNodes (F : Name) (counter : IO.Ref Nat) (t : Expr) : CoreM Name := do
  let i ← counter.modifyGet fun n => (n, n + 1)
  let name := F ++ Name.mkSimple s!"n{i}"
  let trace := mkConst ``Trace
  let val ← if t.isAppOfArity ``Trace.event 2 then
      let c ← addNodes F counter t.appArg!
      pure (mkApp2 (mkConst ``Trace.event) t.appFn!.appArg! (mkConst c))
    else if t.isAppOfArity ``Trace.cases 1 then
      let some (_, ts) := t.appArg!.listLit? | throwError "isla_nodes: cases not a list"
      let cs ← ts.mapM (addNodes F counter)
      pure (mkApp (mkConst ``Trace.cases)
        (cs.foldr (fun c l => mkApp3 (mkConst ``List.cons [Level.zero]) trace (mkConst c) l)
          (mkApp (mkConst ``List.nil [Level.zero]) trace)))
    else pure t
  addDecl (.defnDecl {
    name := name, levelParams := [], type := trace, value := val,
    hints := ReducibilityHints.abbrev, safety := DefinitionSafety.safe })
  return name

open Lean Elab Command in
/-- `isla_nodes F` defines `F.n0`, `F.n1`, and so on, one for each node of the trace of the
footprint `F`, each naming the nodes below it, with `F.n0` the whole trace.  A walk's hypothesis
or goal then holds one event and the name of the rest. -/
elab "isla_nodes " id:ident : command => liftCoreM do
  let F ← realizeGlobalConstNoOverloadWithInfo id
  let some v := (← getConstInfo F).value? | throwError "isla_nodes: {F} has no value"
  unless v.isAppOfArity ``Footprint.mk 3 do throwError "isla_nodes: {F} is not a literal"
  discard <| addNodes F (← IO.mkRef 0) v.appArg!

/-- A proposition that `omega` does not take apart. -/
def Opaque (p : Prop) : Prop := p

theorem Opaque.out {p : Prop} (h : Opaque p) : p := h

open Lean Meta in
/-- The conjuncts of `t`, a right-nested conjunction, with their proofs from `h`. -/
partial def conjuncts (t h : Expr) : MetaM (List (Expr × Expr)) := do
  if t.isAppOfArity ``And 2 then
    let a := t.appFn!.appArg!
    let b := t.appArg!
    return (a, mkApp3 (mkConst ``And.left) a b h) ::
      (← conjuncts b (mkApp3 (mkConst ``And.right) a b h))
  else return [(t, h)]

open Lean Meta in
/-- The conjunction of the propositions `ps`, with its proof from the proofs of the parts. -/
def mkConj : List (Expr × Expr) → Expr × Expr
  | [] => (mkConst ``True, mkConst ``True.intro)
  | [p] => p
  | (a, ha) :: ps =>
    let (b, hb) := mkConj ps
    (mkApp2 (mkConst ``And) a b, mkApp4 (mkConst ``And.intro) a b ha hb)

open Lean Elab Command Term Meta in
/-- `isla_ctx F π` defines `F.ctx σ u`, the premise of `Agrees` on the registers `σ` outside the
model for the footprint `F` and the profile `π u` as `isla_reads` evaluates it, each equation once,
wrapped in `Opaque`.  It proves `F.ctx_of`, which derives `F.ctx σ u` from the premise.  The proofs
over `F` then share one evaluation of the trace's reads, hold one equation for each register that
the trace reads instead of one for each read, and keep the equations from `omega`. -/
elab "isla_ctx " F:ident ppSpace π:term : command => do
  let Fn ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo F
  let Fid := mkIdent Fn
  liftTermElabM do
    let stx ← `(fun (σ : Sys) (u : Unknown)
        (hσ : ∀ q ∈ ($Fid).trace.reads, σ.get q.1 q.2 = ($π u).get q.1 q.2) =>
        (show _ by
          isla_reads [$Fid:ident, Profile.sys_get, Profile.sys, tcg, kvm, sme] at hσ
          exact hσ))
    let e ← instantiateMVars (← elabTermAndSynthesize stx none)
    if e.hasMVar then throwError "isla_ctx: unassigned metavariables"
    let ty ← instantiateMVars (← inferType e)
    let ctxName := Fn ++ `ctx
    let (ctxVal, thmVal) ← forallTelescope ty fun xs body => do
      let parts ← conjuncts body (mkAppN e xs)
      let uniq := parts.foldl (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []
      let (t, h) := mkConj uniq
      return (← mkLambdaFVars #[xs[0]!, xs[1]!] (mkApp (mkConst ``Opaque) t),
        ← mkLambdaFVars xs h)
    addDecl (.defnDecl {
      name := ctxName, levelParams := [], type := ← inferType ctxVal, value := ctxVal,
      hints := ReducibilityHints.regular 0, safety := DefinitionSafety.safe })
    let thmType ← forallTelescope ty fun xs _ =>
      mkForallFVars xs (mkApp2 (mkConst ctxName) xs[0]! xs[1]!)
    addDecl (.thmDecl {
      name := Fn ++ `ctx_of, levelParams := [], type := thmType, value := thmVal })

/-- The natural number of an optional bit vector, 0 otherwise. -/
def witBits : Option Val → Nat
  | some (.bits _ n) => n
  | _ => 0

/-- The Boolean of an optional Boolean, `false` otherwise. -/
def witBool : Option Val → Bool
  | some (.bool b) => b
  | _ => false

/-- Element `j` of a vector. -/
def vecAt (j : Nat) : Val → Option Val
  | .vec vs => vs[j]?
  | _ => none

/-- The `k` bytes of `m` at the address `y`, as a bit vector. -/
def memAt (m : UInt64 → UInt8) (k : Nat) : Val → Option Val
  | .bits 64 y => some (.bits (8 * k) (bytes m (.ofNat y) k))
  | _ => none

section Meta

open Lean Meta Elab Tactic

/-- Whether `b`, a `Base`, is the variable `x`. -/
def isVarE (x : Nat) (b : Expr) : Bool :=
  b.isAppOfArity ``Base.var 1 && b.appArg!.nat? == some x

/-- The strings of a list literal of string literals. -/
def strList? (e : Expr) : Option (List String) := do
  let (_, xs) ← e.listLit?
  xs.mapM fun x => match x with
    | .lit (.strVal s) => some s
    | _ => none

/-- Where the variable `x` lies in the register value `v`: at a path of fields, or at an index of
a vector. -/
def rvalPath? (x : Nat) (v : Expr) : Option (List String ⊕ Nat) :=
  if v.isAppOfArity ``RVal.base 1 then
    if isVarE x v.appArg! then some (.inl []) else none
  else if v.isAppOfArity ``RVal.struct 1 then do
    let (_, fs) ← v.appArg!.listLit?
    fs.findSome? fun p =>
      if p.isAppOfArity ``Prod.mk 4 && isVarE x p.appArg! then
        match p.appFn!.appArg! with
        | .lit (.strVal f) => some (.inl [f])
        | _ => none
      else none
  else if v.isAppOfArity ``RVal.vec 1 then do
    let (_, bs) ← v.appArg!.listLit?
    let j ← bs.findIdx? (isVarE x)
    some (.inr j)
  else none

/-- The event that reads a declared variable: a read or reset of the register `r` at the accessor
path `al`, holding the variable at `path` of its value; a read of memory at `a` of `k` bytes;
register `j` in the values that a vector primitive lists; or the result of the abstract function
`f` on the arguments `args`. -/
inductive Bind where
  | reg (assume : Bool) (r al : Expr) (path : List String ⊕ Nat)
  | mem (a k : Expr)
  | gpr (j : Nat)
  | abs (f args : Expr)

/-- The first event of the trace `t`, in the order of its paths, that reads the variable `x`. -/
partial def findBind (x : Nat) (t : Expr) : MetaM (Option Bind) := do
  if let .const c _ := t then
    let some v := (← getConstInfo c).value? | return none
    return ← findBind x v
  if t.isAppOfArity ``Trace.event 2 then
    let e := t.appFn!.appArg!
    let here : Option Bind :=
      if e.isAppOfArity ``Event.readReg 3 || e.isAppOfArity ``Event.assumeReg 3 then
        let args := e.getAppArgs
        (rvalPath? x args[2]!).map
          (.reg (e.isAppOfArity ``Event.assumeReg 3) args[0]! args[1]!)
      else if e.isAppOfArity ``Event.readMem 3 then
        let args := e.getAppArgs
        if isVarE x args[0]! then some (.mem args[1]! args[2]!) else none
      else if e.isAppOfArity ``Event.readGprs 3 || e.isAppOfArity ``Event.writeGprs 3 then do
        let (_, xs) ← e.appArg!.listLit?
        let j ← xs.findIdx? (isVarE x)
        some (.gpr j)
      else if e.isAppOfArity ``Event.abstractCall 3 then
        let args := e.getAppArgs
        if isVarE x args[1]! then some (.abs args[0]! args[2]!) else none
      else none
    match here with
    | some b => return some b
    | none => findBind x t.appArg!
  else if t.isAppOfArity ``Trace.cases 1 then
    let some (_, ts) := t.appArg!.listLit? | return none
    for b in ts do
      if let some r ← findBind x b then return some r
    return none
  else return none

/-- The value of a declared variable that the event `b` reads from the state `s` and the
registers `σ`, with the variables `ρ` and the meanings `A` of the abstract functions, or 0 or
`true` when no event reads it.  A free Boolean
of the traces selects among the results of `ConstrainUnpredictable`, and the path of an unaligned
access that splits it into bytes asserts the first, `Constraint_NONE`. -/
def witness (isBool : Bool) (b : Option Bind) (A ρ s σ : Expr) : MetaM Expr := do
  let some b := b | return if isBool then mkConst ``Bool.true else mkNatLit 0
  let opt ← match b with
    | .reg assume r al path =>
      let get ← mkAppM ``regGet #[s, σ, r, al]
      match path with
      | .inl q =>
        let q' ← if assume then pure q else
          match strList? al with
          | some al' => pure (q.drop al'.length)
          | none => throwError "mem_wit: accessor path not a literal"
        mkAppM ``Option.bind #[get, ← mkAppM ``acc #[toExpr q']]
      | .inr j => mkAppM ``Option.bind #[get, ← mkAppM ``vecAt #[mkNatLit j]]
    | .mem a k =>
      mkAppM ``Option.bind #[← mkAppM ``Base.eval #[ρ, a],
        ← mkAppM ``memAt #[← mkAppM ``State.mem #[s], k]]
    | .gpr j =>
      mkAppM ``GetElem?.getElem? #[← mkAppM ``gprVals #[s], mkNatLit j]
    | .abs f args =>
      mkAppM ``Option.bind #[← mkAppM ``RVal.evalAll #[ρ, args], mkApp A f]
  mkAppM (if isBool then ``witBool else ``witBits) #[opt]

/-- Gives the variable that a goal
`∃ n, n < 2 ^ w ∧ Trace.Run P A t (ρ.set x (.bits w n)) s σ o`, or
`∃ b, Trace.Run P A t (ρ.set x (.bool b)) s σ o`, declares the value that the first event of `t`
reading it reads. -/
elab "mem_wit" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let_expr Exists ty p := tgt | throwError "mem_wit: not an existential"
  let .lam _ _ body _ := p | throwError "mem_wit: not a lambda"
  let run := if body.isAppOfArity ``And 2 then body.appArg! else body
  unless run.isAppOfArity ``Trace.Run 7 do throwError "mem_wit: not a path"
  let args := run.getAppArgs
  let ρ' := args[3]!
  unless ρ'.isAppOfArity ``Vars.set 3 do throwError "mem_wit: no declaration"
  let ρ := ρ'.appFn!.appFn!.appArg!
  let some x := ρ'.appFn!.appArg!.nat? | throwError "mem_wit: variable not a literal"
  if ρ.hasLooseBVars || args[4]!.hasLooseBVars || args[5]!.hasLooseBVars then
    throwError "mem_wit: the state depends on the witness"
  let w ← witness (ty.isConstOf ``Bool) (← findBind x args[2]!) args[1]! ρ args[4]! args[5]!
  let stx ← Term.exprToSyntax w
  evalTactic (← `(tactic| refine ⟨$stx, ?_⟩))

/-- The path that `e` states, with its node constant replaced by the node's definition. -/
def unfoldRun (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  unless e.isAppOfArity ``Trace.Run 7 do throwError "mem_unfold: not a path"
  let args := e.getAppArgs
  let .const c _ := args[2]! | throwError "mem_unfold: not a node"
  let some v := (← getConstInfo c).value? | throwError "mem_unfold: {c} has no value"
  return mkAppN e.getAppFn (args.set! 2 v)

/-- Replaces the node constant of the path that the goal, or the hypothesis `h`, states by the
node's definition. -/
syntax "mem_unfold" (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| mem_unfold) => withMainContext do
    let g ← getMainGoal
    let ty ← unfoldRun (← instantiateMVars (← g.getType))
    replaceMainGoal [← g.replaceTargetDefEq ty]
  | `(tactic| mem_unfold at $h:ident) => withMainContext do
    let g ← getMainGoal
    let decl ← getLocalDeclFromUserName h.getId
    let ty ← unfoldRun (← instantiateMVars decl.type)
    replaceMainGoal [← g.replaceLocalDeclDefEq decl.fvarId ty]

/-- Clears the hypotheses with inaccessible names, which a walk introduces, so that `omega` at the
end of a path reads only the theorem's facts. -/
elab "mem_clear" : tactic => withMainContext do
  let mut g ← getMainGoal
  let decls := (← getLCtx).foldl (fun acc d =>
    if !d.isImplementationDetail && d.userName.hasMacroScopes then acc.push d.fvarId else acc) #[]
  for f in decls.reverse do
    try g ← g.clear f catch _ => pure ()
  replaceMainGoal [g]

/-- Rewrites the hypothesis `h` with the equation `x` between a variable and a term, replacing the
variable by the term.  `subst` would also rewrite every other hypothesis that mentions the
variable, hundreds of them late in a walk. -/
elab "mem_subst " x:ident " at " h:ident : tactic => withMainContext do
  let xd ← getLocalDeclFromUserName x.getId
  let some (_, a, b) := (← instantiateMVars xd.type).eq? | throwError "mem_subst: no equation"
  if a.isFVar && !b.containsFVar a.fvarId! then
    evalTactic (← `(tactic| rw [$x:ident] at $h:ident))
  else if b.isFVar && !a.containsFVar b.fvarId! then
    evalTactic (← `(tactic| rw [← $x:ident] at $h:ident))
  else throwError "mem_subst: no variable"

/-- `omega` without the facts that a walk introduces, which all have inaccessible names: the side
conditions of the walk's rules follow from the theorem's facts, and the walk's facts, hundreds of
them with terms of the address translation, make each call of `omega` slow. -/
elab "mem_omega" : tactic => withMainContext do
  let g ← getMainGoal
  let mut lctx ← getLCtx
  for d in lctx do
    if !d.isImplementationDetail && d.userName.hasMacroScopes && (← isProp d.type) then
      lctx := lctx.erase d.fvarId
  let g' ← mkFreshExprMVarAt lctx (← getLocalInstances) (← g.getType) .syntheticOpaque
  g.assign g'
  replaceMainGoal [g'.mvarId!]
  evalTactic (← `(tactic| omega))

end Meta

/-! The masks of the address translation.  The walk computes a descriptor's address from
`TTBR0_NS` and the virtual address with the masks below, and the physical address of an access
in the RAM GiB as `0x40000000 ||| (va &&& 0x3fffffff)`. -/

theorem and_mul_two_pow (x c k : Nat) : x &&& c * 2 ^ k = (x / 2 ^ k &&& c) * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases h : k ≤ i
  · simp only [decide_eq_true h, Bool.true_and, Nat.sub_add_cancel h]
  · simp only [decide_eq_false h, Bool.false_and, Bool.and_false]

theorem or_mul_two_pow {a b k : Nat} (hb : b < 2 ^ k) : a * 2 ^ k ||| b = a * 2 ^ k + b := by
  rw [Nat.mul_comm a]
  exact (Nat.two_pow_add_eq_or_of_lt hb a).symm

/-- The mask constraint on `TTBR0_NS`: a multiple of 32 in the RAM GiB. -/
theorem ttbr_facts {a : Nat} (h : a &&& 18446744072635809823 = 1073741824) (ha : a < 2 ^ 64) :
    a % 32 = 0 ∧ a / 1073741824 = 1 := by
  have and_eq : ∀ m, m &&& 18446744072635809823 = m → a &&& m = 1073741824 &&& m := by
    intro m hm
    calc a &&& m = a &&& (18446744072635809823 &&& m) := by
          rw [Nat.and_comm 18446744072635809823, hm]
      _ = 1073741824 &&& m := by rw [← Nat.and_assoc, h]
  have h31 : a &&& 31 = 0 := (and_eq 31 (by decide)).trans (by decide)
  have h32 : a % 32 = a &&& 31 := (Nat.and_two_pow_sub_one_eq_mod a 5).symm
  have hs : a >>> 30 &&& 17179869183 = 1 := by
    have := congrArg (· >>> 30) h
    simpa only [Nat.shiftRight_and_distrib, Nat.reduceShiftRight] using this
  have hm : a >>> 30 &&& 17179869183 = a >>> 30 % 2 ^ 34 := Nat.and_two_pow_sub_one_eq_mod _ 34
  rw [hm, Nat.shiftRight_eq_div_pow] at hs
  exact ⟨by omega, by omega⟩

theorem and_c0 {x : Nat} (h1 : 1073741824 ≤ x) (h2 : x < 2147483648) :
    x &&& 3221225472 = 1073741824 := by
  rw [show (3221225472 : Nat) = 3 * 2 ^ 30 from rfl, and_mul_two_pow,
    show x / 2 ^ 30 = 1 by omega]
  rfl

theorem and_c0_low {x : Nat} (h : x < 1073741824) : x &&& 3221225472 = 0 := by
  rw [show (3221225472 : Nat) = 3 * 2 ^ 30 from rfl, and_mul_two_pow,
    show x / 2 ^ 30 = 0 by omega, Nat.zero_and, Nat.zero_mul]

theorem and_hi_zero {x c k : Nat} (h : x < 2 ^ k) : x &&& c * 2 ^ k = 0 := by
  rw [and_mul_two_pow, Nat.div_eq_of_lt h, Nat.zero_and, Nat.zero_mul]

theorem and_ffffffff00000000 {x : Nat} (h : x < 4294967296) :
    x &&& 18446744069414584320 = 0 :=
  and_hi_zero (c := 4294967295) (k := 32) h

theorem and_ffffff00000000 {x : Nat} (h : x < 4294967296) : x &&& 72057589742960640 = 0 :=
  and_hi_zero (c := 16777215) (k := 32) h

theorem and_3fffffff (x : Nat) : x &&& 1073741823 = x % 1073741824 :=
  Nat.and_two_pow_sub_one_eq_mod x 30

theorem or_40000000 {y : Nat} (h : y < 1073741824) : 1073741824 ||| y = 1073741824 + y := by
  have := or_mul_two_pow (a := 1) (k := 30) h
  simpa only [Nat.one_mul, Nat.reducePow] using this

theorem or_lt32 {x b : Nat} (hx : x % 32 = 0) (hb : b < 32) : x ||| b = x + b := by
  have := or_mul_two_pow (a := x / 32) (k := 5) hb
  rw [show x / 32 * 2 ^ 5 = x by omega] at this
  exact this

/-- The high half of the 128-bit `_TTBR0_EL1`, which the walk joins to `TTBR0_NS`. -/
theorem and_hi64 (a : Nat) :
    a &&& 340282366920938463444927863358058659840 =
      a / 18446744073709551616 % 18446744073709551616 * 18446744073709551616 := by
  rw [show (340282366920938463444927863358058659840 : Nat) =
      (2 ^ 64 - 1) * 2 ^ 64 from rfl, and_mul_two_pow, Nat.and_two_pow_sub_one_eq_mod]

theorem or_lo64 {a b : Nat} (hb : b < 18446744073709551616) :
    a * 18446744073709551616 ||| b = a * 18446744073709551616 + b :=
  or_mul_two_pow (k := 64) hb

/-- The physical address of an access in the RAM GiB. -/
theorem pa_eq {x : Nat} (h1 : 1073741824 ≤ x) (h2 : x < 2147483648) :
    1073741824 + x % 72057594037927936 % 1073741824 = x := by
  omega

/-- The physical address of an access in the GiB from 0. -/
theorem pa0_eq {x : Nat} (h : x < 1073741824) : x % 72057594037927936 % 1073741824 = x := by
  omega

/-! Memory: bounds on the bytes that a trace reads, a byte store as the model's `store8`, and the
bytes that a store leaves unchanged. -/

theorem bytes_lt1 (m : UInt64 → UInt8) (a : UInt64) : bytes m a 1 < 256 := by
  have := UInt8.toNat_lt (m a)
  simp only [bytes, Nat.mul_zero, Nat.add_zero]
  omega

theorem bytes_lt8 (m : UInt64 → UInt8) (a : UInt64) : bytes m a 8 < 18446744073709551616 := by
  rw [← load64_toNat]
  exact toNat_lt _

/-- `writeBytes` of one byte is `store8`. -/
theorem writeBytes_one (m : UInt64 → UInt8) (a : UInt64) (x : Nat) :
    writeBytes m a x 1 = store8 m a (UInt8.ofNat (x % 256)) := rfl

theorem ofNat_mod64 (x : Nat) : UInt64.ofNat (x % 18446744073709551616) = UInt64.ofNat x :=
  UInt64.ofNat_mod_size

/-- Two memories that agree on the `k` bytes from `a` give `bytes` the same value there. -/
theorem bytes_congr {m m' : UInt64 → UInt8} : ∀ {k : Nat} {a : UInt64},
    (∀ i < k, m (a + UInt64.ofNat i) = m' (a + UInt64.ofNat i)) → bytes m a k = bytes m' a k
  | 0, _, _ => rfl
  | k + 1, a, h => by
    have h0 := h 0 (Nat.succ_pos k)
    rw [show a + UInt64.ofNat 0 = a from UInt64.add_zero a] at h0
    simp only [bytes]
    rw [h0, bytes_congr (k := k) (a := a + 1) fun i hi => ?_]
    have e : a + 1 + UInt64.ofNat i = a + UInt64.ofNat (i + 1) := by
      apply UInt64.toNat_inj.mp
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', UInt64.reduceToNat, Nat.reducePow]
      omega
    rw [e]
    exact h (i + 1) (by omega)

/-- A byte store outside the eight bytes from `y` leaves their `bytes`, as the walk of the
translation table after a byte of an unaligned store reads them. -/
theorem bytes_store_far (P : Platform) (s : State) {y z : Nat} (x : Nat)
    (hyz : z + 1 ≤ y ∨ y + 8 ≤ z) (hy : y + 8 ≤ 18446744073709551616)
    (hz : z < 18446744073709551616) :
    bytes (store P s (UInt64.ofNat z) x 1).mem (UInt64.ofNat y) 8 =
      bytes s.mem (UInt64.ofNat y) 8 := by
  unfold store
  split
  · rfl
  · apply bytes_congr
    intro i hi
    have hne : ¬ UInt64.ofNat y + UInt64.ofNat i = UInt64.ofNat z := by
      intro h
      have := congrArg UInt64.toNat h
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat', Nat.reducePow] at this
      omega
    simp only [writeBytes, hne, ↓reduceIte]

/-! The premises in the walk's terms. -/

theorem spAligned_31 {s : State} {n : Fin 32} (h : n.val = 31) (ha : s.spAligned n = true) :
    s.sp.toNat % 16 = 0 := by
  simp only [State.spAligned, h, bne_self_eq_false, Bool.false_or, beq_iff_eq] at ha
  have := congrArg UInt64.toNat ha
  simpa only [UInt64.toNat_mod, UInt64.reduceToNat] using this

theorem ttbr_toNat {x : BitVec 64} (h : x &&& 0xffffffffc000001f#64 = 0x40000000#64) :
    x.toNat &&& 18446744072635809823 = 1073741824 := by
  have := congrArg BitVec.toNat h
  simpa only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] using this

/-- The descriptor at the table's address plus 8, as the walk's read checks it. -/
theorem desc_eq {m : UInt64 → UInt8} {t : Nat} {d : UInt64} (h : load64 m (.ofNat t + 8) = d) :
    ∀ y, y = t + 8 → bytes m (.ofNat y) 8 = d.toNat := by
  intro y hy
  rw [← load64_toNat, ← h, hy, UInt64.ofNat_add]
  rfl

/-- The descriptor at the table's address, as the walk's read checks it. -/
theorem desc0_eq {m : UInt64 → UInt8} {t : Nat} {d : UInt64} (h : load64 m (.ofNat t) = d) :
    ∀ y, y = t → bytes m (.ofNat y) 8 = d.toNat := by
  intro y hy
  rw [← load64_toNat, ← h, hy]

/-- Evaluates the events of a walk: the rules of `isla_simp` with `reduceVars` and `reduceGpr` in
place of the lookups of variables and registers, the lemmas on the masks, `bytes_store_far`, and
the lemmas in brackets, among them the premise on the registers outside the model. -/
syntax "mem_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? :
  tactic
macro_rules
  | `(tactic| mem_simp [$xs,*] $(loc)?) => `(tactic| simp -failIfUnchanged (maxSteps := 4000000)
      (disch := mem_omega) only [
      Exp.eval, Base.eval, RVal.eval, Base.evalAll, Base.evalFields, Unop.apply, Binop.apply,
      Binop.arith, lshr, regGet, regSet, part, reduceGpr, gprs, partGet, partPut, bit, acc, upd,
      gprVals, Trace.RunSome, reduceVars, Sys.set_apply, Sys.get_set, List.lookup, Option.bind,
      Option.map, Option.getD, Val.bits.injEq, Val.bool.injEq, Val.enum.injEq, Val.struct.injEq,
      Val.vec.injEq, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, List.map_cons,
      List.map_nil, List.cons_append, List.nil_append, eq_self_iff_true, decide_eq_true_eq,
      decide_eq_false_iff_not, Bool.not_eq_true', Bool.not_not, Bool.not_true, Bool.not_false,
      Bool.and_true, Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or,
      Bool.or_false, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, and_true, true_and,
      and_self, and_assoc, ne_eq, not_true_eq_false, not_false_eq_true, false_and, and_false,
      or_false, false_or, Nat.pow_zero, Nat.div_one, Nat.mod_mod, nat_add_zero, Nat.zero_add,
      Nat.zero_mul, fin_mod, fin_div, toNat_mod, toNat_mod128, Fin.is_lt, ↓reduceIte,
      ↓reduceDIte, reduceCtorEq, String.reduceEq, String.reduceNe, String.reduceBEq,
      String.reduceAppend, String.reduceToList, Char.reduceBEq, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceBEq, Bool.cond_true, Bool.cond_false,
      decide_true, decide_false, chain_eq, sysreg, bv, sdiv_128, sint, witBits, witBool, vecAt,
      memAt, List.getElem?_cons, and_hi64, or_lo64, and_c0, and_c0_low, or_lt32, and_3fffffff,
      or_40000000, and_ffffffff00000000, and_ffffff00000000, pa_eq, pa0_eq, bytes_lt1, bytes_lt8,
      bytes_store_far, $xs,*] $(loc)?)

/-- Takes the hypothesis `h`, that a path of a trace ends in an outcome, through the trace, as
`isla_fwd` does: it unfolds the node of each step, evaluates its event with `mem_simp` and the
lemmas in brackets, splits the disjunctions of `cases`, takes apart the existentials of
`declare-const` and the conjunctions of reads and asserts, substitutes each variable by the value
that a read gives in `h`, and proves the condition of each `assume` with the tactic after
`using`. -/
syntax "mem_fwd " ident " using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| mem_fwd $h using $d with [$xs,*]) => `(tactic| repeat' (first
      | (mem_unfold at $h:ident; rw [Trace.Run] at $h:ident; mem_simp [$xs,*] at $h:ident)
      | (guard_hyp $h : False; exact False.elim $h)
      | (guard_hyp $h : Or _ _; rcases $h:ident with $h:ident | $h:ident)
      | (guard_hyp $h : Exists _; obtain ⟨x, $h:ident⟩ := $h:ident)
      | (guard_hyp $h : And _ _
         obtain ⟨x, $h:ident⟩ := $h:ident
         first
           | mem_subst x at $h:ident
           | (guard_hyp x : _ = UInt64.toNat (regAt _ _)
              rw [x] at $h:ident
              mem_simp [$xs,*] at $h:ident)
           | skip)
      | (guard_hyp $h : @Eq Outcome _ _; subst $h:ident)
      | focus (rw [ite_eq_left] at $h:ident; rotate_left; ($d))))

/-- Builds a path of a trace: it unfolds the node of each step, evaluates its event with
`mem_simp` and the lemmas in brackets, gives each declared variable its value with `mem_wit`,
takes the branch of each `cases` whose first condition the tactic after `using` proves or `simp`
leaves true, leaves the condition of each read or assert as a later goal, and proves the condition
of each `assume` with the tactic after `using`. -/
syntax "mem_bwd " "using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mem_bwd using $d with [$xs,*]) => `(tactic| repeat (first
      | (mem_unfold; rw [Trace.Run]; mem_simp [$xs,*])
      | (guard_target = Exists _; mem_wit)
      | (guard_target = Or _ _
         first
           | (apply Or.inl
              mem_unfold
              rw [Trace.Run]
              mem_simp [$xs,*]
              fail_if_success guard_target = False
              first
                | (guard_target = And _ _; refine ⟨by $d, ?_⟩)
                | guard_target = Trace.Run _ _ _ _ _ _ _)
           | apply Or.inr)
      | (guard_target = And _ _; apply And.intro; rotate_left)
      | focus (rw [ite_eq_left]; rotate_left; ($d))))

/-- Proves a goal that `mem_bwd` leaves: the bound of a declared variable's value, or the
condition of a read or an assert, with the premise `hσ` and the lemmas in brackets. -/
syntax "mem_side " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| mem_side $hσ [$xs,*]) => `(tactic| first
      | (mem_simp [Opaque.out $hσ, $xs,*]; done)
      | (mem_simp [Opaque.out $hσ, $xs,*]
         first | exact toNat_lt _ | exact BitVec.isLt _ | exact bit_lt _ | omega))

/-- The fields of a load or store for the registers `t` and `n` and the immediate `imm`. -/
def memFields (t n : Fin 32) (imm : Fin 4096) : Fields :=
  [("imm12", imm.val), ("Rn", n.val), ("Rt", t.val)]

end LeanExe.A64.Isla
