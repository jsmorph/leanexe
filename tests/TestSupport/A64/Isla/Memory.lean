import LeanExe.A64.Isla.Check
import LeanExe.A64.Isla.Profile

/-!
Theorems of `Agrees` for the load and store forms of `LeanExe/A64/Machine.lean`: `LDR`, `STR`,
and `STRB` in the RAM GiB, and `STRB` at the UART's data register, for every value of the fields
`imm12`, `Rn`, and `Rt`, register 31 included.  The traces are those of `tests/isla/tcg` and
`tests/isla/kvm` with the arguments `memory`, under the profiles `tcg` and `kvm`.  The two traces of
a form differ: under `kvm`, FEAT_LSE2 lets an unaligned access within 16 bytes run as one access,
and the exception entry of the alignment fault writes more fields of `PSTATE`, so each form has a
proof under each profile.

A theorem states the constraints that the trace's `assume` events and fixed reads check as
premises in the model's terms.  The mask constraint of `traces.sh` puts `u.ttbr0`, the value of
`TTBR0_NS`, at a multiple of 32 in the RAM GiB.  The memory holds the descriptors of
`LeanExe/A64/Table.lean` that the walk reads: `0x0040000040000705` at `u.ttbr0 + 8` for an access
in the RAM GiB, and `0x0060000000000401` at `u.ttbr0` for the UART's.  The access's address,
register `Rn`, the stack pointer for 31, plus the scaled immediate, lies where the reset
constraint puts it: every byte in the RAM GiB, or at `0x09000000`.  On a misaligned stack pointer
`exec` fails, so the paths to the alignment fault's exception entry need no counterpart, and every
other path writes `SEE` and no other register outside the model.

`STR` needs two more premises.  An unaligned doubleword store under `tcg`, or one that crosses a
16-byte boundary under `kvm`, writes its bytes one at a time and translates the address of each
byte after storing the bytes before it.  Reading 5 of `Trace.lean` sends a byte written at
`P.uart` to the output, while `exec` stores all eight bytes in memory, so the UART's byte must lie
outside Normal memory.  The walk for each later byte reads the descriptor at `u.ttbr0 + 8` from
the memory as the earlier stores left it, so the eight bytes must lie clear of that descriptor.
A byte store at `0x09000000` appends the byte to the output when `P.uart` is `0x09000000`, in the
trace through reading 5 and in `exec` through its case of the UART.  For any other `P.uart`, both
store the byte in memory, so the theorems of the UART leave `P` open.

The proofs walk the traces with the tactics of this module.  `isla_nodes F` gives each node of the
trace of `F` a definition that names the nodes below it, so that a path's hypothesis or goal holds
one event and the name of the rest, and a step of the walk costs the size of an event instead of
the size of the trace.  `isla_ctx F π` evaluates the premise of `Agrees` on the registers outside
the model once for each footprint.  `mem_fwd` takes a path's hypothesis through the trace, and
`mem_bwd` builds the path to `exec`'s state, giving each declared variable, through `mem_wit`,
the value that the first event reading it reads.  The address translation computes with masks
that are literals of the traces, and lemmas on those literals reduce it to linear arithmetic for
`omega`.  A load that runs byte by byte inserts its eight bytes one at a time into a word, and
`ins_chain` gives the word's value at the end of the path.  Rewriting each insertion during the
walk would write the word twice per byte, so the term's tree would double at each of the eight
bytes.  Each theorem rests on lemmas for the four cases of register 31 among `Rn` and `Rt`, one
for each direction.
-/

namespace TestSupport.A64.Isla

open LeanExe.A64 LeanExe.A64.Isla

/- The lemmas elaborate one after another, so that the peak of memory is that of one lemma's walk
instead of that of all the lemmas that would elaborate at once. -/
set_option Elab.async false

/-! The walk of a trace. -/

/-- Simp enters neither the trace of a path nor its variables, which a walk extends with values
that `simp` already evaluated. -/
@[congr] theorem run_congr {P : Platform} {t : Trace} {ρ : Vars} {s s' : State} {σ σ' : Sys}
    {o o' : Outcome} (h2 : s = s') (h3 : σ = σ') (h4 : o = o') :
    Trace.Run P t ρ s σ o = Trace.Run P t ρ s' σ' o' := by
  subst h2 h3 h4
  rfl

@[congr] theorem runSome_congr {P : Platform} {ts : List Trace} {ρ : Vars} {s s' : State}
    {σ σ' : Sys} {o o' : Outcome} (h2 : s = s') (h3 : σ = σ') (h4 : o = o') :
    Trace.RunSome P ts ρ s σ o = Trace.RunSome P ts ρ s' σ' o' := by
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
          isla_reads [$Fid:ident, Profile.sys_get, Profile.sys, tcg, kvm] at hσ
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
path `al`, holding the variable at `path` of its value; a read of memory at `a` of `k` bytes; or
register `j` in the values that a vector primitive lists. -/
inductive Bind where
  | reg (assume : Bool) (r al : Expr) (path : List String ⊕ Nat)
  | mem (a k : Expr)
  | gpr (j : Nat)

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
registers `σ`, with the variables `ρ`, or 0 or `true` when no event reads it.  A free Boolean
of the traces selects among the results of `ConstrainUnpredictable`, and the path of an unaligned
access that splits it into bytes asserts the first, `Constraint_NONE`. -/
def witness (isBool : Bool) (b : Option Bind) (ρ s σ : Expr) : MetaM Expr := do
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
  mkAppM (if isBool then ``witBool else ``witBits) #[opt]

/-- Gives the variable that a goal
`∃ n, n < 2 ^ w ∧ Trace.Run P t (ρ.set x (.bits w n)) s σ o`, or
`∃ b, Trace.Run P t (ρ.set x (.bool b)) s σ o`, declares the value that the first event of `t`
reading it reads. -/
elab "mem_wit" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let_expr Exists ty p := tgt | throwError "mem_wit: not an existential"
  let .lam _ _ body _ := p | throwError "mem_wit: not a lambda"
  let run := if body.isAppOfArity ``And 2 then body.appArg! else body
  unless run.isAppOfArity ``Trace.Run 6 do throwError "mem_wit: not a path"
  let args := run.getAppArgs
  let ρ' := args[2]!
  unless ρ'.isAppOfArity ``Vars.set 3 do throwError "mem_wit: no declaration"
  let ρ := ρ'.appFn!.appFn!.appArg!
  let some x := ρ'.appFn!.appArg!.nat? | throwError "mem_wit: variable not a literal"
  if ρ.hasLooseBVars || args[3]!.hasLooseBVars || args[4]!.hasLooseBVars then
    throwError "mem_wit: the state depends on the witness"
  let w ← witness (ty.isConstOf ``Bool) (← findBind x args[1]!) ρ args[3]! args[4]!
  let stx ← Term.exprToSyntax w
  evalTactic (← `(tactic| refine ⟨$stx, ?_⟩))

/-- The path that `e` states, with its node constant replaced by the node's definition. -/
def unfoldRun (e : Expr) : MetaM Expr := do
  let e := e.consumeMData.headBeta
  unless e.isAppOfArity ``Trace.Run 6 do throwError "mem_unfold: not a path"
  let args := e.getAppArgs
  let .const c _ := args[1]! | throwError "mem_unfold: not a node"
  let some v := (← getConstInfo c).value? | throwError "mem_unfold: {c} has no value"
  return mkAppN e.getAppFn (args.set! 1 v)

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

/-- Runs the tactics without recording their info trees.  A walk takes thousands of steps, and the
info tree of each step holds its goals and metavariable contexts, which the elaboration of a file
keeps to its end. -/
elab "mem_quiet " t:tacticSeq : tactic => withEnableInfoTree false (evalTactic t)

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

/-- SMT-LIB's `bvsdiv` of 128 bits on operands below the sign bit, as the alignment checks use
it. -/
theorem sdiv_128 {a b : Nat} (ha : a < 170141183460469231731687303715884105728)
    (hb : b < 170141183460469231731687303715884105728) (hb0 : 0 < b) : sdiv 128 a b = a / b := by
  have h : (2 : Nat) ^ 128 = 340282366920938463463374607431768211456 := by decide
  unfold sdiv udiv
  rw [h, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem toNat_mod128 (a : UInt64) :
    a.toNat % 340282366920938463463374607431768211456 = a.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_trans (toNat_lt a) (by decide))

theorem bit_lt (b : Bool) : (if b = true then 1 else 0) < 2 := by
  cases b <;> decide

/-! Memory: the bytes that the trace reads and writes as the model's `load64`, `store64`, and
`store8`. -/

theorem bytes_lt1 (m : UInt64 → UInt8) (a : UInt64) : bytes m a 1 < 256 := by
  have := UInt8.toNat_lt (m a)
  simp only [bytes, Nat.mul_zero, Nat.add_zero]
  omega

theorem bytes_lt8 (m : UInt64 → UInt8) (a : UInt64) : bytes m a 8 < 18446744073709551616 := by
  rw [← load64_toNat]
  exact toNat_lt _

/-- The eight bytes of a load as one-byte loads, as an unaligned load reads them. -/
theorem bytes_split (m : UInt64 → UInt8) (a : UInt64) :
    bytes m a 8 = bytes m a 1 + bytes m (a + 1) 1 * 256 + bytes m (a + 2) 1 * 65536 +
      bytes m (a + 3) 1 * 16777216 + bytes m (a + 4) 1 * 4294967296 +
      bytes m (a + 5) 1 * 1099511627776 + bytes m (a + 6) 1 * 281474976710656 +
      bytes m (a + 7) 1 * 72057594037927936 := by
  simp only [bytes, UInt64.add_assoc, UInt64.reduceAdd]
  omega

theorem add_left_inj' (a d e : UInt64) : a + d = a + e ↔ d = e := by
  constructor
  · intro h
    have := congrArg (· - a) h
    simpa only [UInt64.add_comm a, UInt64.add_sub_cancel] using this
  · intro h
    rw [h]

theorem add_eq_self (a d : UInt64) : a + d = a ↔ d = 0 := by
  have := add_left_inj' a d 0
  rwa [UInt64.add_zero] at this

theorem add_sub_left' (a d : UInt64) : a + d - a = d := by
  rw [UInt64.add_comm, UInt64.add_sub_cancel]

theorem eq_add_sub (a b : UInt64) : b = a + (b - a) := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_add, UInt64.toNat_sub]
  have := toNat_lt a
  have := toNat_lt b
  omega

theorem byteOf_eq (v : UInt64) (k : Nat) (hk : k < 8) :
    byteOf v k = UInt8.ofNat (v.toNat / 2 ^ (8 * k) % 256) := by
  apply UInt8.toNat_inj.mp
  have h1 : 8 * k % 2 ^ 64 % 64 = 8 * k := by omega
  simp only [byteOf, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat',
    UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, h1, Nat.reducePow, Nat.mod_mod]

/-- Eight byte stores from `a`, the lowest byte first, are `store64`. -/
theorem store8_chain (m : UInt64 → UInt8) (a v : UInt64) :
    store8 (store8 (store8 (store8 (store8 (store8 (store8 (store8 m a (byteOf v 0))
      (a + 1) (byteOf v 1)) (a + 2) (byteOf v 2)) (a + 3) (byteOf v 3)) (a + 4) (byteOf v 4))
      (a + 5) (byteOf v 5)) (a + 6) (byteOf v 6)) (a + 7) (byteOf v 7) = store64 m a v := by
  funext b
  rw [eq_add_sub a b]
  generalize b - a = d
  simp only [store8, store64, add_left_inj', add_eq_self, add_sub_left']
  by_cases h0 : d = 0
  · subst h0; rfl
  by_cases h1 : d = 1
  · subst h1; rfl
  by_cases h2 : d = 2
  · subst h2; rfl
  by_cases h3 : d = 3
  · subst h3; rfl
  by_cases h4 : d = 4
  · subst h4; rfl
  by_cases h5 : d = 5
  · subst h5; rfl
  by_cases h6 : d = 6
  · subst h6; rfl
  by_cases h7 : d = 7
  · subst h7; rfl
  have h8 : ¬ d < 8 := by
    intro h
    rw [UInt64.lt_iff_toNat_lt] at h
    simp only [← UInt64.toNat_inj] at h0 h1 h2 h3 h4 h5 h6 h7
    simp only [UInt64.reduceToNat] at h h0 h1 h2 h3 h4 h5 h6 h7
    omega
  simp only [h0, h1, h2, h3, h4, h5, h6, h7, h8, ↓reduceIte]

/-- `writeBytes` of one byte is `store8`. -/
theorem writeBytes_one (m : UInt64 → UInt8) (a : UInt64) (x : Nat) :
    writeBytes m a x 1 = store8 m a (UInt8.ofNat (x % 256)) := rfl

/-- `writeBytes` of eight bytes is eight byte stores. -/
theorem writeBytes_eight (m : UInt64 → UInt8) (a : UInt64) (x : Nat) :
    writeBytes m a x 8 =
      store8 (store8 (store8 (store8 (store8 (store8 (store8 (store8 m a (.ofNat (x % 256)))
        (a + 1) (.ofNat (x / 256 % 256))) (a + 2) (.ofNat (x / 65536 % 256)))
        (a + 3) (.ofNat (x / 16777216 % 256))) (a + 4) (.ofNat (x / 4294967296 % 256)))
        (a + 5) (.ofNat (x / 1099511627776 % 256))) (a + 6) (.ofNat (x / 281474976710656 % 256)))
        (a + 7) (.ofNat (x / 72057594037927936 % 256)) := by
  funext b
  simp only [writeBytes, store8, UInt64.add_assoc, UInt64.reduceAdd, Nat.div_div_eq_div_mul,
    Nat.reduceMul]

theorem toUInt8_eq (x : UInt64) : x.toUInt8 = UInt8.ofNat (x.toNat % 256) := by
  apply UInt8.toNat_inj.mp
  simp only [UInt64.toNat_toUInt8, UInt8.toNat_ofNat', Nat.reducePow, Nat.mod_mod]

theorem ofNat_mod64 (x : Nat) : UInt64.ofNat (x % 18446744073709551616) = UInt64.ofNat x :=
  UInt64.ofNat_mod_size

/-! Inserting a byte into a word, as an unaligned load assembles its value from one-byte loads:
`(y &&& ~(0xff << k)) ||| (b << k)`. -/

theorem and_mod64 {y M : Nat} (hM : 18446744073709551615 &&& M = M) :
    y &&& M = y % 18446744073709551616 &&& M := by
  calc y &&& M = y &&& (18446744073709551615 &&& M) := by rw [hM]
    _ = (y &&& 18446744073709551615) &&& M := (Nat.and_assoc _ _ _).symm
    _ = y % 18446744073709551616 &&& M := by
        rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl,
          Nat.and_two_pow_sub_one_eq_mod]

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

/-- The address `x + c` as the trace computes it, with the immediate `c` reduced modulo
`2 ^ 64`. -/
theorem addr_eq (x : UInt64) (c : Nat) :
    UInt64.ofNat ((x.toNat + c % 18446744073709551616) % 18446744073709551616) =
      x + UInt64.ofNat c := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add, Nat.reducePow, Nat.mod_mod]

/-- The address `x + c + i` of byte `i` of an access, as the trace computes it. -/
theorem addr_add (x : UInt64) (c i : Nat) :
    UInt64.ofNat (((x.toNat + c % 18446744073709551616) % 18446744073709551616 + i) %
      18446744073709551616) = x + (UInt64.ofNat c + UInt64.ofNat i) := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add, Nat.reducePow, Nat.mod_mod]
  omega

theorem testBit_lo {lo k j : Nat} (hlo : lo < 2 ^ k) (hj : k ≤ j) : lo.testBit j = false :=
  Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlo (Nat.pow_le_pow_right (by decide) hj))

/-- Replacing byte `k / 8` of a word, in digits: the low `k` bits `lo`, the byte `d`, and the
high bits `hi`. -/
theorem ins_core {lo d hi b k : Nat} (hlo : lo < 2 ^ k) (hd : d < 2 ^ 8) (hb : b < 2 ^ 8)
    (hhi : hi < 2 ^ (56 - k)) :
    (2 ^ k * (2 ^ 8 * hi + d) + lo) &&& (2 ^ k * (2 ^ 8 * (2 ^ (56 - k) - 1) + 0) + (2 ^ k - 1)) |||
      (2 ^ k * (2 ^ 8 * 0 + b) + 0) = 2 ^ k * (2 ^ 8 * hi + b) + lo := by
  apply Nat.eq_of_testBit_eq
  intro j
  have h0 : (0 : Nat) < 2 ^ k := Nat.two_pow_pos k
  have h1 : 2 ^ k - 1 < 2 ^ k := by omega
  have h08 : (0 : Nat) < 2 ^ 8 := by decide
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_two_pow_mul_add _ hlo,
    Nat.testBit_two_pow_mul_add _ h1, Nat.testBit_two_pow_mul_add _ h0,
    Nat.testBit_two_pow_mul_add _ hlo]
  by_cases hj : j < k
  · simp only [hj, ↓reduceIte, Nat.testBit_two_pow_sub_one, decide_true, Bool.and_true,
      Nat.zero_testBit, Bool.or_false]
  · simp only [hj, ↓reduceIte]
    rw [Nat.testBit_two_pow_mul_add _ hd, Nat.testBit_two_pow_mul_add _ h08,
      Nat.testBit_two_pow_mul_add _ hb, Nat.testBit_two_pow_mul_add _ hb]
    by_cases hj8 : j - k < 8
    · simp only [hj8, ↓reduceIte, Nat.zero_testBit, Bool.and_false, Bool.false_or]
    · simp only [hj8, ↓reduceIte, Nat.zero_testBit, Nat.testBit_two_pow_sub_one, Bool.or_false]
      by_cases hj2 : j - k - 8 < 56 - k
      · simp only [hj2, decide_true, Bool.and_true]
      · simp only [hj2, decide_false, Bool.and_false]
        exact (testBit_lo hhi (by omega)).symm

/-- `ins_core` for a word `y` below `2 ^ 64`. -/
theorem ins_byte {y b k : Nat} (hy : y < 2 ^ 64) (hb : b < 2 ^ 8) (hk : k ≤ 56) :
    y &&& (2 ^ k * (2 ^ 8 * (2 ^ (56 - k) - 1) + 0) + (2 ^ k - 1)) |||
      (2 ^ k * (2 ^ 8 * 0 + b) + 0) =
      2 ^ k * (2 ^ 8 * (y / 2 ^ k / 2 ^ 8) + b) + y % 2 ^ k := by
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have e1 : y = 2 ^ k * (2 ^ 8 * (y / 2 ^ k / 2 ^ 8) + y / 2 ^ k % 2 ^ 8) + y % 2 ^ k := by
    rw [Nat.div_add_mod (y / 2 ^ k) (2 ^ 8), Nat.div_add_mod y (2 ^ k)]
  have hhi : y / 2 ^ k / 2 ^ 8 < 2 ^ (56 - k) := by
    rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (Nat.mul_pos hpos (by decide)),
      ← Nat.pow_add, ← Nat.pow_add, show 56 - k + (k + 8) = 64 by omega]
    exact hy
  conv => lhs; rw [e1]
  exact ins_core (Nat.mod_lt _ hpos) (Nat.mod_lt _ (by decide)) hb hhi


/-- Inserting byte 0 of a load into a word, as the unaligned load writes it. -/
theorem ins_0 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446744073709551360 ||| bytes m a 1 =
      bytes m a 1 + y % 18446744073709551616 / 256 * 256 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 0) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.mul_zero, Nat.zero_add,
    Nat.add_zero, Nat.one_mul, Nat.div_one, Nat.mod_one] at this
  rw [this]
  omega

/-- Inserting byte 1 of a load into a word, as the unaligned load writes it. -/
theorem ins_8 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446744073709486335 ||| bytes m a 1 * 256 % 18446744073709551616 =
      y % 256 + bytes m a 1 * 256 +
        y % 18446744073709551616 / 65536 * 65536 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 8) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 256 % 18446744073709551616 =
      256 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 2 of a load into a word, as the unaligned load writes it. -/
theorem ins_16 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446744073692839935 ||| bytes m a 1 * 65536 % 18446744073709551616 =
      y % 65536 + bytes m a 1 * 65536 +
        y % 18446744073709551616 / 16777216 * 16777216 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 16) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 65536 % 18446744073709551616 =
      65536 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 3 of a load into a word, as the unaligned load writes it. -/
theorem ins_24 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446744069431361535 ||| bytes m a 1 * 16777216 % 18446744073709551616 =
      y % 16777216 + bytes m a 1 * 16777216 +
        y % 18446744073709551616 / 4294967296 * 4294967296 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 24) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 16777216 % 18446744073709551616 =
      16777216 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 4 of a load into a word, as the unaligned load writes it. -/
theorem ins_32 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446742978492891135 ||| bytes m a 1 * 4294967296 % 18446744073709551616 =
      y % 4294967296 + bytes m a 1 * 4294967296 +
        y % 18446744073709551616 / 1099511627776 * 1099511627776 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 32) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 4294967296 % 18446744073709551616 =
      4294967296 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 5 of a load into a word, as the unaligned load writes it. -/
theorem ins_40 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18446463698244468735 ||| bytes m a 1 * 1099511627776 % 18446744073709551616 =
      y % 1099511627776 + bytes m a 1 * 1099511627776 +
        y % 18446744073709551616 / 281474976710656 * 281474976710656 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 40) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 1099511627776 % 18446744073709551616 =
      1099511627776 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 6 of a load into a word, as the unaligned load writes it. -/
theorem ins_48 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 18374967954648334335 ||| bytes m a 1 * 281474976710656 % 18446744073709551616 =
      y % 281474976710656 + bytes m a 1 * 281474976710656 +
        y % 18446744073709551616 / 72057594037927936 * 72057594037927936 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 48) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 281474976710656 % 18446744073709551616 =
      281474976710656 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- Inserting byte 7 of a load into a word, as the unaligned load writes it. -/
theorem ins_56 (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    y &&& 72057594037927935 ||| bytes m a 1 * 72057594037927936 % 18446744073709551616 =
      y % 72057594037927936 + bytes m a 1 * 72057594037927936 +
        y % 18446744073709551616 / 18446744073709551616 * 18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [and_mod64 (by decide)]
  have := ins_byte (k := 56) (y := y % 18446744073709551616) (b := bytes m a 1)
    (Nat.mod_lt _ (by decide)) hb (by decide)
  simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul,
    Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.div_div_eq_div_mul] at this
  have e : bytes m a 1 * 72057594037927936 % 18446744073709551616 =
      72057594037927936 * bytes m a 1 := by omega
  rw [e, this]
  omega

/-- The low byte of a word after the insertion of byte 0. -/
theorem ins_base (y : Nat) (m : UInt64 → UInt8) (a : UInt64) :
    (y &&& 18446744073709551360 ||| bytes m a 1) % 256 = bytes m a 1 ∧
      (y &&& 18446744073709551360 ||| bytes m a 1) < 18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_0]
  omega

/-- The low bytes of a word after the insertion of byte 1, from those before it. -/
theorem ins_step_8 {v l : Nat} (h : v % 256 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446744073709486335 ||| bytes m a 1 * 256 % 18446744073709551616) %
        65536 = l + bytes m a 1 * 256 ∧
      v &&& 18446744073709486335 ||| bytes m a 1 * 256 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_8]
  omega

/-- The low bytes of a word after the insertion of byte 2, from those before it. -/
theorem ins_step_16 {v l : Nat} (h : v % 65536 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446744073692839935 ||| bytes m a 1 * 65536 % 18446744073709551616) %
        16777216 = l + bytes m a 1 * 65536 ∧
      v &&& 18446744073692839935 ||| bytes m a 1 * 65536 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_16]
  omega

/-- The low bytes of a word after the insertion of byte 3, from those before it. -/
theorem ins_step_24 {v l : Nat} (h : v % 16777216 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446744069431361535 ||| bytes m a 1 * 16777216 % 18446744073709551616) %
        4294967296 = l + bytes m a 1 * 16777216 ∧
      v &&& 18446744069431361535 ||| bytes m a 1 * 16777216 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_24]
  omega

/-- The low bytes of a word after the insertion of byte 4, from those before it. -/
theorem ins_step_32 {v l : Nat} (h : v % 4294967296 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446742978492891135 ||| bytes m a 1 * 4294967296 % 18446744073709551616) %
        1099511627776 = l + bytes m a 1 * 4294967296 ∧
      v &&& 18446742978492891135 ||| bytes m a 1 * 4294967296 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_32]
  omega

/-- The low bytes of a word after the insertion of byte 5, from those before it. -/
theorem ins_step_40 {v l : Nat} (h : v % 1099511627776 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18446463698244468735 ||| bytes m a 1 * 1099511627776 % 18446744073709551616) %
        281474976710656 = l + bytes m a 1 * 1099511627776 ∧
      v &&& 18446463698244468735 ||| bytes m a 1 * 1099511627776 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_40]
  omega

/-- The low bytes of a word after the insertion of byte 6, from those before it. -/
theorem ins_step_48 {v l : Nat} (h : v % 281474976710656 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 18374967954648334335 ||| bytes m a 1 * 281474976710656 % 18446744073709551616) %
        72057594037927936 = l + bytes m a 1 * 281474976710656 ∧
      v &&& 18374967954648334335 ||| bytes m a 1 * 281474976710656 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_48]
  omega

/-- The low bytes of a word after the insertion of byte 7, from those before it. -/
theorem ins_step_56 {v l : Nat} (h : v % 72057594037927936 = l) (hv : v < 18446744073709551616)
    (m : UInt64 → UInt8) (a : UInt64) :
    (v &&& 72057594037927935 ||| bytes m a 1 * 72057594037927936 % 18446744073709551616) %
        18446744073709551616 = l + bytes m a 1 * 72057594037927936 ∧
      v &&& 72057594037927935 ||| bytes m a 1 * 72057594037927936 % 18446744073709551616 <
        18446744073709551616 := by
  have hb := bytes_lt1 m a
  rw [ins_56]
  omega

/-- The word that an unaligned load assembles from its eight bytes, inserted one by one into the
word `y`, is their value as `bytes_split` writes it. -/
theorem ins_chain (y : Nat) (m : UInt64 → UInt8) (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) :
    (((((((y &&& 18446744073709551360 ||| bytes m a0 1) &&& 18446744073709486335 |||
      bytes m a1 1 * 256 % 18446744073709551616) &&& 18446744073692839935 |||
      bytes m a2 1 * 65536 % 18446744073709551616) &&& 18446744069431361535 |||
      bytes m a3 1 * 16777216 % 18446744073709551616) &&& 18446742978492891135 |||
      bytes m a4 1 * 4294967296 % 18446744073709551616) &&& 18446463698244468735 |||
      bytes m a5 1 * 1099511627776 % 18446744073709551616) &&& 18374967954648334335 |||
      bytes m a6 1 * 281474976710656 % 18446744073709551616) &&& 72057594037927935 |||
      bytes m a7 1 * 72057594037927936 % 18446744073709551616 =
      bytes m a0 1 + bytes m a1 1 * 256 + bytes m a2 1 * 65536 + bytes m a3 1 * 16777216 +
        bytes m a4 1 * 4294967296 + bytes m a5 1 * 1099511627776 +
        bytes m a6 1 * 281474976710656 + bytes m a7 1 * 72057594037927936 := by
  obtain ⟨e0, l0⟩ := ins_base y m a0
  obtain ⟨e1, l1⟩ := ins_step_8 e0 l0 m a1
  obtain ⟨e2, l2⟩ := ins_step_16 e1 l1 m a2
  obtain ⟨e3, l3⟩ := ins_step_24 e2 l2 m a3
  obtain ⟨e4, l4⟩ := ins_step_32 e3 l3 m a4
  obtain ⟨e5, l5⟩ := ins_step_40 e4 l4 m a5
  obtain ⟨e6, l6⟩ := ins_step_48 e5 l5 m a6
  obtain ⟨e7, l7⟩ := ins_step_56 e6 l6 m a7
  exact (Nat.mod_eq_of_lt l7).symm.trans e7


/-! The model's side: the stack pointer as register 31 of a base, the premises in the walk's
terms, and `exec` of each form. -/

theorem xsp_lt {s : State} {n : Fin 32} (h : n.val < 31) : s.xsp n = regAt s n.val := by
  unfold State.xsp regAt
  rw [dite_eq_left h, dite_eq_left h]

theorem xsp_31 {s : State} {n : Fin 32} (h : n.val = 31) : s.xsp n = s.sp := by
  unfold State.xsp
  rw [dite_eq_right (by omega)]

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

/-- A byte of the eight from `a` is not the UART's when the eight are Normal memory and the
UART's is not. -/
theorem mapped_uart {P : Platform} {a : UInt64} (hm : P.mapped a 8 = true)
    (hP : P.normal P.uart = false) (i : Nat) (hi : i < 8) : ¬ a + UInt64.ofNat i = P.uart := by
  intro h
  have : P.normal (a + UInt64.ofNat i) = true := by
    simp only [Platform.mapped, List.all_eq_true, List.mem_range] at hm
    exact hm i hi
  rw [h, hP] at this
  cases this

/-- `exec` of a byte store: the stack pointer's check passes, and the state appends the byte to
the output at the UART and stores it elsewhere. -/
theorem exec_strb {P : Platform} {t n : Fin 32} {imm : Fin 4096} {s s' : State}
    (hs : exec P (.strb t n imm) s = some s') : s.spAligned n = true ∧
      s' = if s.xsp n + .ofNat imm.val = P.uart then
          { s with out := s.out ++ [(s.x t).toUInt8], pc := s.pc + 4 }
        else
          { s with mem := store8 s.mem (s.xsp n + .ofNat imm.val) (s.x t).toUInt8,
                   pc := s.pc + 4 } := by
  simp only [exec] at hs
  split at hs
  · cases hs
  · rename_i h1
    refine ⟨by simpa using h1, ?_⟩
    split at hs
    · rename_i hu
      rw [ite_eq_left hu]
      exact (Option.some.inj hs).symm
    · rename_i hu
      rw [ite_eq_right hu]
      split at hs
      · exact (Option.some.inj hs).symm
      · cases hs

/-- `exec` of a doubleword store: the stack pointer's check passes, the eight bytes are Normal
memory, and the state stores register `t` there. -/
theorem exec_str {P : Platform} {t n : Fin 32} {imm : Fin 4096} {s s' : State}
    (hs : exec P (.str t n imm) s = some s') : s.spAligned n = true ∧
      P.mapped (s.xsp n + .ofNat (8 * imm.val)) 8 = true ∧
      s' = { s with mem := store64 s.mem (s.xsp n + .ofNat (8 * imm.val)) (s.x t),
                    pc := s.pc + 4 } := by
  simp only [exec] at hs
  split at hs
  · rename_i h1
    rw [Bool.and_eq_true] at h1
    exact ⟨h1.1, h1.2, (Option.some.inj hs).symm⟩
  · cases hs

/-- `exec` of a doubleword load: the stack pointer's check passes, and the state loads the eight
bytes into register `t`. -/
theorem exec_ldr {P : Platform} {t n : Fin 32} {imm : Fin 4096} {s s' : State}
    (hs : exec P (.ldr t n imm) s = some s') : s.spAligned n = true ∧
      s' = { s.setX t (load64 s.mem (s.xsp n + .ofNat (8 * imm.val))) with pc := s.pc + 4 } := by
  simp only [exec] at hs
  split at hs
  · rename_i h1
    rw [Bool.and_eq_true] at h1
    exact ⟨h1.1, (Option.some.inj hs).symm⟩
  · cases hs

open Lean Meta in
/-- The subterms `bytes m a 1` of `e`. -/
partial def byteTerms (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``bytes 3 && e.appArg!.nat? == some 1 && !acc.contains e then
    acc.push e else acc
  match e with
  | .app f a => byteTerms a (byteTerms f acc)
  | .lam _ t b _ | .forallE _ t b _ => byteTerms b (byteTerms t acc)
  | .letE _ t v b _ => byteTerms b (byteTerms v (byteTerms t acc))
  | .mdata _ b | .proj _ _ b => byteTerms b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- Adds `bytes m a 1 < 256` for each subterm `bytes m a 1` of the goal, for `omega`. -/
elab "mem_bounds" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let hs ← (byteTerms tgt #[]).mapM fun e => do
    let args := e.getAppArgs
    let pf ← mkAppM ``bytes_lt1 #[args[0]!, args[1]!]
    return { userName := `hb, type := ← inferType pf, value := pf : Hypothesis }
  let (_, g) ← (← getMainGoal).assertHypotheses hs
  replaceMainGoal [g]

/-- `Nat.add_zero` with a proof that is not definitional.  `simp` applies `Nat.add_zero`, a `rfl`
theorem, without a proof step, so the kernel checks `x + 0 = x` by unfolding.  For the table's
address in the walk for the UART, a remainder of a 128-bit term, that check ran for more than nine
minutes and took 8 GiB. -/
theorem nat_add_zero (n : Nat) : n + 0 = n := by omega

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
                | guard_target = Trace.Run _ _ _ _ _ _)
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

/-- Proves that the outcome `finish s₁ σ₁` at the end of a path of a byte store is `exec`'s,
whose state `hs` states. -/
syntax "strb_end " term:max : tactic
macro_rules
  | `(tactic| strb_end $hs) => `(tactic| (
    simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true]
    rw [$hs:term]
    split
    all_goals
      rename_i hu
      simp (disch := omega) only [xsp_lt, xsp_31] at hu
      simp (disch := omega) only [store, writeBytes_one, ofNat_mod64, UInt64.ofNat_add,
        UInt64.ofNat_toNat, xsp_lt, xsp_31, x_lt, x_31, toUInt8_eq, Nat.mod_mod, State.mk.injEq,
        List.append_cancel_left_eq, List.cons.injEq, and_true, true_and, and_self, ↓reduceIte,
        Nat.reducePow, UInt64.reduceToNat, Nat.zero_mod, hu]))

/-- Proves that the outcome `finish s₁ σ₁` at the end of a path of a doubleword store is
`exec`'s, whose state `hs` states, with the facts in brackets that no byte of the store is the
UART's. -/
syntax "str_end " term:max " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| str_end $hs [$xs,*]) => `(tactic| (
    simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true]
    rw [$hs:term]
    simp (disch := omega) only [store, writeBytes_one, writeBytes_eight, ofNat_mod64,
      UInt64.ofNat_add, UInt64.ofNat_toNat, UInt64.reduceOfNat, UInt64.add_zero, UInt64.add_assoc,
      UInt64.reduceAdd, xsp_lt, xsp_31, x_lt, x_31, ← store8_chain, byteOf_eq, Nat.reducePow,
      Nat.reduceMul, Nat.div_one, Nat.mod_mod, UInt64.reduceToNat, Nat.zero_div, Nat.zero_mod,
      State.mk.injEq, and_true, true_and, and_self, ↓reduceIte, Nat.reduceEqDiff, and_false,
      $xs,*]))

/-- Proves that the outcome `finish s₁ σ₁` at the end of a path of a doubleword load is `exec`'s,
whose state `hs` states.  An unaligned load inserts its bytes one by one into a word, and
`ins_chain` gives the word's value. -/
syntax "ldr_end " term:max : tactic
macro_rules
  | `(tactic| ldr_end $hs) => `(tactic| (
    simp only [finish, Sys.set_apply, String.reduceEq, ↓reduceIte, Outcome.done.injEq, and_true]
    rw [$hs:term]
    simp (disch := omega) only [setX_eq_setRegAt, setRegAt_pc, load64_eq, addr_eq, addr_add,
      ins_chain, bytes_split, UInt64.reduceOfNat, UInt64.add_zero, UInt64.add_assoc,
      UInt64.reduceAdd, xsp_lt, xsp_31, setRegAt_31, setRegAt_lt, State.mk.injEq, and_true,
      true_and, and_self]))

/-- The fields of a load or store for the registers `t` and `n` and the immediate `imm`. -/
def memFields (t n : Fin 32) (imm : Fin 4096) : Fields :=
  [("imm12", imm.val), ("Rn", n.val), ("Rt", t.val)]

set_option maxRecDepth 100000 in
/-- The footprint of `LDR Xt, [Xn|SP, #(8 * imm)]` in RAM under `tcg`. -/
def ldrTcg : Footprint := isla_trace% "tests/isla/tcg/ldr"

isla_nodes ldrTcg

set_option maxRecDepth 100000 in
theorem ldrTcg_n0 : ldrTcg.trace = ldrTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ldrTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : ldrTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    ldrTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldr_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    ldrTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldr_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : ldrTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    ldrTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals
      mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
      all_goals first
        | exact hT
        | (apply Eq.symm; ldr_end hs'; done)
        | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    ldrTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrTcg_n0, show ldrTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals
      mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
      all_goals first
        | exact hT
        | (apply Eq.symm; ldr_end hs'; done)
        | mem_side hσ [hn, ht]

/-- The trace of `LDR Xt, [Xn|SP, #(8 * imm)]` in the RAM GiB under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem ldr_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] ldrTcg (memFields t n imm)
      (.ldr t n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : ldrTcg.opcode.word (memFields t n imm) = encodeNat (.ldr t n imm) := by
      rw [show ldrTcg.opcode = [.bits 10 0b1111100101, .field "imm12" 12, .field "Rn" 5,
        .field "Rt" 5] from rfl]
      simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · have hc := ldrTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrTcg_fwd_sp_zr hc httbr ha hs hn ht h
      · exact ldrTcg_fwd_sp_r hc httbr ha hs hn ht h
      · exact ldrTcg_fwd_x_zr hc httbr ha hs hn ht h
      · exact ldrTcg_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrTcg_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact ldrTcg_bwd_sp_r hc httbr hd ha hs hn ht
      · exact ldrTcg_bwd_x_zr hc httbr hd ha hs hn ht
      · exact ldrTcg_bwd_x_r hc httbr hd ha hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `LDR Xt, [Xn|SP, #(8 * imm)]` in RAM under `kvm`. -/
def ldrKvm : Footprint := isla_trace% "tests/isla/kvm/ldr"

isla_nodes ldrKvm

set_option maxRecDepth 100000 in
theorem ldrKvm_n0 : ldrKvm.trace = ldrKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx ldrKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : ldrKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    ldrKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldr_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    ldrKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; ldr_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem ldrKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : ldrKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem ldrKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    ldrKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals by_cases hg : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 16 ≤ 8
    all_goals
      first
        | (exfalso; omega)
        | (mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
           all_goals first
             | exact hT
             | (apply Eq.symm; ldr_end hs'; done)
             | mem_side hσ [hn, ht])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `ldrKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem ldrKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : ldrKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; ldr_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `ldrKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem ldrKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : ldrKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.ldr t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    ldrKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_ldr hs
    rw [Nat.mul_comm 8 imm.val] at ha hs'
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [ldrKvm_n0, show ldrKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals by_cases hg : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 16 ≤ 8
    all_goals
      first
        | (exfalso; omega)
        | (mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
           all_goals first
             | exact hT
             | (apply Eq.symm; ldr_end hs'; done)
             | mem_side hσ [hn, ht])

/-- The trace of `LDR Xt, [Xn|SP, #(8 * imm)]` in the RAM GiB under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem ldr_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] ldrKvm (memFields t n imm)
      (.ldr t n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : ldrKvm.opcode.word (memFields t n imm) = encodeNat (.ldr t n imm) := by
      rw [show ldrKvm.opcode = [.bits 10 0b1111100101, .field "imm12" 12, .field "Rn" 5,
        .field "Rt" 5] from rfl]
      simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · have hc := ldrKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 630),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrKvm_fwd_sp_zr hc httbr ha hs hn ht h
      · exact ldrKvm_fwd_sp_r hc httbr ha hs hn ht h
      · exact ldrKvm_fwd_x_zr hc httbr ha hs hn ht h
      · exact ldrKvm_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact ldrKvm_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact ldrKvm_bwd_sp_r hc httbr hd ha hs hn ht
      · exact ldrKvm_bwd_x_zr hc httbr hd ha hs hn ht
      · exact ldrKvm_bwd_x_r hc httbr hd ha hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STR Xt, [Xn|SP, #(8 * imm)]` in RAM under `tcg`. -/
def strTcg : Footprint := isla_trace% "tests/isla/tcg/str"

isla_nodes strTcg

set_option maxRecDepth 100000 in
theorem strTcg_n0 : strTcg.trace = strTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx strTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : strTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    strTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : strTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    strTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : strTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    strTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hov hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hov hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals
      mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
      all_goals first
        | exact hT
        | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
        | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : strTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strTcg.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    strTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hov hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hov hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strTcg_n0, show strTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals
      mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
      all_goals first
        | exact hT
        | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
        | mem_side hσ [hn, ht]

/-- The trace of `STR Xt, [Xn|SP, #(8 * imm)]` in the RAM GiB under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem str_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (hP : P.normal P.uart = false) (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] strTcg (memFields t n imm)
      (.str t n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : strTcg.opcode.word (memFields t n imm) = encodeNat (.str t n imm) := by
      rw [show strTcg.opcode = [.bits 10 0b1111100100, .field "imm12" 12, .field "Rn" 5,
        .field "Rt" 5] from rfl]
      simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · have hc := strTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strTcg_fwd_sp_zr hc hP httbr ha hs hn ht h
      · exact strTcg_fwd_sp_r hc hP httbr ha hs hn ht h
      · exact strTcg_fwd_x_zr hc hP httbr ha hs hn ht h
      · exact strTcg_fwd_x_r hc hP httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strTcg_bwd_sp_zr hc hP httbr hd ha hs hn ht
      · exact strTcg_bwd_sp_r hc hP httbr hd ha hs hn ht
      · exact strTcg_bwd_x_zr hc hP httbr hd ha hov hs hn ht
      · exact strTcg_bwd_x_r hc hP httbr hd ha hov hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STR Xt, [Xn|SP, #(8 * imm)]` in RAM under `kvm`. -/
def strKvm : Footprint := isla_trace% "tests/isla/kvm/str"

isla_nodes strKvm

set_option maxRecDepth 100000 in
theorem strKvm_n0 : strKvm.trace = strKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx strKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : strKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    strKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : strKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    strKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : strKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    strKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hov hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hov hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals by_cases hg : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 16 ≤ 8
    all_goals
      first
        | (exfalso; omega)
        | (mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
           all_goals first
             | exact hT
             | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
             | mem_side hσ [hn, ht])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : strKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648)) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run at h
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strKvm.ctx σ u) (hP : P.normal P.uart = false)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat)
    (hs : exec P (.str t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    strKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648))) := by
  mem_quiet
    obtain ⟨hal, hm, hs'⟩ := exec_str hs
    rw [Nat.mul_comm 8 imm.val] at ha hov hm hs'
    have hu0 := mapped_uart hm hP 0 (by decide)
    have hu1 := mapped_uart hm hP 1 (by decide)
    have hu2 := mapped_uart hm hP 2 (by decide)
    have hu3 := mapped_uart hm hP 3 (by decide)
    have hu4 := mapped_uart hm hP 4 (by decide)
    have hu5 := mapped_uart hm hP 5 (by decide)
    have hu6 := mapped_uart hm hP 6 (by decide)
    have hu7 := mapped_uart hm hP 7 (by decide)
    simp only [UInt64.reduceOfNat, UInt64.add_zero] at hu0
    simp only [UInt64.reduceOfNat, UInt64.add_assoc] at hu1 hu2 hu3 hu4 hu5 hu6 hu7
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat (imm.val * 8)).toNat =
        ((s.xsp n).toNat + imm.val * 8) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha hov hu0 hu1 hu2 hu3 hu4 hu5 hu6 hu7
    unfold Footprint.Run
    rw [strKvm_n0, show strKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    by_cases hal8 : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 8 = 0
    all_goals by_cases hg : ((regAt s n.val).toNat + imm.val * 8) % 18446744073709551616 % 16 ≤ 8
    all_goals
      first
        | (exfalso; omega)
        | (mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
           all_goals first
             | exact hT
             | (apply Eq.symm; str_end hs' [hu0, hu1, hu2, hu3, hu4, hu5, hu6, hu7]; done)
             | mem_side hσ [hn, ht])

/-- The trace of `STR Xt, [Xn|SP, #(8 * imm)]` in the RAM GiB under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem str_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (hP : P.normal P.uart = false) (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat ∧
      (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ 0x7ffffff8)
    (hov : (s.xsp n + .ofNat (8 * imm.val)).toNat ≤ u.ttbr0.toNat ∨
      u.ttbr0.toNat + 16 ≤ (s.xsp n + .ofNat (8 * imm.val)).toNat) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] strKvm (memFields t n imm)
      (.str t n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : strKvm.opcode.word (memFields t n imm) = encodeNat (.str t n imm) := by
      rw [show strKvm.opcode = [.bits 10 0b1111100100, .field "imm12" 12, .field "Rn" 5,
        .field "Rt" 5] from rfl]
      simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · have hc := strKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 648),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strKvm_fwd_sp_zr hc hP httbr ha hs hn ht h
      · exact strKvm_fwd_sp_r hc hP httbr ha hs hn ht h
      · exact strKvm_fwd_x_zr hc hP httbr ha hs hn ht h
      · exact strKvm_fwd_x_r hc hP httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strKvm_bwd_sp_zr hc hP httbr hd ha hs hn ht
      · exact strKvm_bwd_sp_r hc hP httbr hd ha hs hn ht
      · exact strKvm_bwd_x_zr hc hP httbr hd ha hov hs hn ht
      · exact strKvm_bwd_x_r hc hP httbr hd ha hov hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STRB Wt, [Xn|SP, #imm]` in RAM under `tcg`. -/
def strbTcg : Footprint := isla_trace% "tests/isla/tcg/strb"

isla_nodes strbTcg

set_option maxRecDepth 100000 in
theorem strbTcg_n0 : strbTcg.trace = strbTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx strbTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strbTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : strbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strbTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    strbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strbTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : strbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strbTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    strbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strbTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : strbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strbTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    strbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strbTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : strbTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strbTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    strbTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [strbTcg_n0, show strbTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `STRB Wt, [Xn|SP, #imm]` in the RAM GiB under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem strb_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] strbTcg (memFields t n imm)
      (.strb t n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : strbTcg.opcode.word (memFields t n imm) = encodeNat (.strb t n imm) := by
      rw [show strbTcg.opcode = [.bits 10 0b0011100100, .field "imm12" 12, .field "Rn" 5,
        .field "Rt" 5] from rfl]
      simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · have hc := strbTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strbTcg_fwd_sp_zr hc httbr ha hs hn ht h
      · exact strbTcg_fwd_sp_r hc httbr ha hs hn ht h
      · exact strbTcg_fwd_x_zr hc httbr ha hs hn ht h
      · exact strbTcg_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strbTcg_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact strbTcg_bwd_sp_r hc httbr hd ha hs hn ht
      · exact strbTcg_bwd_x_zr hc httbr hd ha hs hn ht
      · exact strbTcg_bwd_x_r hc httbr hd ha hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STRB Wt, [Xn|SP, #imm]` in RAM under `kvm`. -/
def strbKvm : Footprint := isla_trace% "tests/isla/kvm/strb"

isla_nodes strbKvm

set_option maxRecDepth 100000 in
theorem strbKvm_n0 : strbKvm.trace = strbKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx strbKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strbKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31)
    (h : strbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strbKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : t.val = 31) :
    strbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strbKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31)
    (h : strbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strbKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : n.val = 31) (ht : ¬ t.val = 31) :
    strbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem strbKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31)
    (h : strbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem strbKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : t.val = 31) :
    strbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `strbKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem strbKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31)
    (h : strbKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `strbKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem strbKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : strbKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff)
    (hs : exec P (.strb t n imm) s = some s') (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    strbKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [strbKvm_n0, show strbKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `STRB Wt, [Xn|SP, #imm]` in the RAM GiB under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem strb_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat + 8) = 0x0040000040000705)
    (ha : 0x40000000 ≤ (s.xsp n + .ofNat imm.val).toNat ∧
      (s.xsp n + .ofNat imm.val).toNat ≤ 0x7fffffff) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] strbKvm (memFields t n imm)
      (.strb t n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : strbKvm.opcode.word (memFields t n imm) = encodeNat (.strb t n imm) := by
      rw [show strbKvm.opcode = [.bits 10 0b0011100100, .field "imm12" 12, .field "Rn" 5,
        .field "Rt" 5] from rfl]
      simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · have hc := strbKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strbKvm_fwd_sp_zr hc httbr ha hs hn ht h
      · exact strbKvm_fwd_sp_r hc httbr ha hs hn ht h
      · exact strbKvm_fwd_x_zr hc httbr ha hs hn ht h
      · exact strbKvm_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact strbKvm_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact strbKvm_bwd_sp_r hc httbr hd ha hs hn ht
      · exact strbKvm_bwd_x_zr hc httbr hd ha hs hn ht
      · exact strbKvm_bwd_x_r hc httbr hd ha hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STRB Wt, [Xn|SP, #imm]` at the UART under `tcg`. -/
def uartTcg : Footprint := isla_trace% "tests/isla/tcg/strb-uart"

isla_nodes uartTcg

set_option maxRecDepth 100000 in
theorem uartTcg_n0 : uartTcg.trace = uartTcg.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx uartTcg (tcg.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartTcg` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem uartTcg_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : t.val = 31) (h : uartTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartTcg` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem uartTcg_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : t.val = 31) :
    uartTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartTcg` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem uartTcg_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : ¬ t.val = 31) (h : uartTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartTcg` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem uartTcg_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : ¬ t.val = 31) :
    uartTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartTcg` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem uartTcg_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : t.val = 31) (h : uartTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartTcg` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem uartTcg_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : t.val = 31) :
    uartTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartTcg` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem uartTcg_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) (h : uartTcg.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartTcg` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem uartTcg_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartTcg.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    uartTcg.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [uartTcg_n0, show uartTcg.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `STRB Wt, [Xn|SP, #imm]` at the UART's data register under `tcg` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem uart_tcg (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) :
    Agrees P (tcg.sys .memory u) ["SEE", "__BranchTaken"] uartTcg (memFields t n imm)
      (.strb t n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : uartTcg.opcode.word (memFields t n imm) = encodeNat (.strb t n imm) := by
      rw [show uartTcg.opcode = [.bits 10 0b0011100100, .field "imm12" 12, .field "Rn" 5,
        .field "Rt" 5] from rfl]
      simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · have hc := uartTcg.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact uartTcg_fwd_sp_zr hc httbr ha hs hn ht h
      · exact uartTcg_fwd_sp_r hc httbr ha hs hn ht h
      · exact uartTcg_fwd_x_zr hc httbr ha hs hn ht h
      · exact uartTcg_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact uartTcg_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact uartTcg_bwd_sp_r hc httbr hd ha hs hn ht
      · exact uartTcg_bwd_x_zr hc httbr hd ha hs hn ht
      · exact uartTcg_bwd_x_r hc httbr hd ha hs hn ht

set_option maxRecDepth 100000 in
/-- The footprint of `STRB Wt, [Xn|SP, #imm]` at the UART under `kvm`. -/
def uartKvm : Footprint := isla_trace% "tests/isla/kvm/strb-uart"

isla_nodes uartKvm

set_option maxRecDepth 100000 in
theorem uartKvm_n0 : uartKvm.trace = uartKvm.n0 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
isla_ctx uartKvm (kvm.sys .memory)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartKvm` for `Rn` = 31 and `Rt` = 31 end in `exec`'s state. -/
theorem uartKvm_fwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : t.val = 31) (h : uartKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartKvm` for `Rn` = 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem uartKvm_bwd_sp_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : t.val = 31) :
    uartKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartKvm` for `Rn` = 31 and `Rt` < 31 end in `exec`'s state. -/
theorem uartKvm_fwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : ¬ t.val = 31) (h : uartKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run at h
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartKvm` for `Rn` = 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem uartKvm_bwd_sp_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : n.val = 31) (ht : ¬ t.val = 31) :
    uartKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    have hsp : s.sp.toNat / 16 * 16 = s.sp.toNat := by
      have := spAligned_31 hn hal
      omega
    rw [xsp_31 hn] at hx ha
    unfold Footprint.Run
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hsp, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartKvm` for `Rn` < 31 and `Rt` = 31 end in `exec`'s state. -/
theorem uartKvm_fwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : t.val = 31) (h : uartKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartKvm` for `Rn` < 31 and `Rt` = 31 has a path to `exec`'s state. -/
theorem uartKvm_bwd_x_zr {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : t.val = 31) :
    uartKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The paths of `uartKvm` for `Rn` < 31 and `Rt` < 31 end in `exec`'s state. -/
theorem uartKvm_fwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} {o : Outcome} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) (h : uartKvm.Run P (memFields t n imm) s σ o) :
    o = .done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651)) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run at h
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl] at h
    mem_fwd h using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht]
    all_goals (mem_clear; strb_end hs')

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- `uartKvm` for `Rn` < 31 and `Rt` < 31 has a path to `exec`'s state. -/
theorem uartKvm_bwd_x_r {P : Platform} {u : Unknown} {t n : Fin 32} {imm : Fin 4096}
    {s s' : State} {σ : Sys} (hσ : uartKvm.ctx σ u)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) (hs : exec P (.strb t n imm) s = some s')
    (hn : ¬ n.val = 31) (ht : ¬ t.val = 31) :
    uartKvm.Run P (memFields t n imm) s σ
      (.done s' ((σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651))) := by
  mem_quiet
    obtain ⟨hal, hs'⟩ := exec_strb hs
    have hT := ttbr_toNat httbr
    obtain ⟨hT32, hT30⟩ := ttbr_facts hT u.ttbr0.isLt
    have hdesc := desc0_eq hd
    simp only [UInt64.reduceToNat] at hdesc
    have := n.isLt
    have := t.isLt
    have := imm.isLt
    have : u.ttbr0.toNat < 18446744073709551616 := u.ttbr0.isLt
    have : u.ttbr0el1.toNat < 340282366920938463463374607431768211456 := u.ttbr0el1.isLt
    have : s.sp.toNat < 18446744073709551616 := toNat_lt _
    have : (regAt s n.val).toNat < 18446744073709551616 := toNat_lt _
    have hx : (s.xsp n + .ofNat imm.val).toNat =
        ((s.xsp n).toNat + imm.val) % 18446744073709551616 := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      simp only [Nat.reducePow]
      omega
    rw [xsp_lt (by omega)] at hx ha
    unfold Footprint.Run
    rw [uartKvm_n0, show uartKvm.vars (memFields t n imm) =
      Vars.set (Vars.set (Vars.set (fun _ => none) 0 (.bits 12 imm.val)) 1
        (.bits 5 n.val)) 2 (.bits 5 t.val) from rfl]
    mem_bwd using (first | mem_omega | exact hT) with [Opaque.out hσ, hn, ht, hdesc]
    all_goals first
      | exact hT
      | (apply Eq.symm; strb_end hs'; done)
      | mem_side hσ [hn, ht]

/-- The trace of `STRB Wt, [Xn|SP, #imm]` at the UART's data register under `kvm` agrees
with `exec` for every value of the fields, register 31 included, from every state that meets the
configuration's constraints. -/
theorem uart_kvm (P : Platform) (u : Unknown) (t n : Fin 32) (imm : Fin 4096) (s : State)
    (httbr : u.ttbr0 &&& 0xffffffffc000001f#64 = 0x40000000#64)
    (hd : load64 s.mem (.ofNat u.ttbr0.toNat) = 0x0060000000000401)
    (ha : (s.xsp n + .ofNat imm.val).toNat = 0x09000000) :
    Agrees P (kvm.sys .memory u) ["SEE", "__BranchTaken"] uartKvm (memFields t n imm)
      (.strb t n imm) s := by
  refine ⟨by decide, by decide, ?_, fun σ hσ s' hs => ?_⟩
  · have h : uartKvm.opcode.word (memFields t n imm) = encodeNat (.strb t n imm) := by
      rw [show uartKvm.opcode = [.bits 10 0b0011100100, .field "imm12" 12, .field "Rn" 5,
        .field "Rt" 5] from rfl]
      simp only [Opcode.word, Opcode.wordFrom, memFields, encodeNat, List.lookup,
        String.reduceBEq, Option.getD, Nat.reducePow, Nat.reduceMul, Nat.reduceAdd]
      omega
    rw [h]
    exact decode_encode _
  · have hc := uartKvm.ctx_of σ u hσ
    refine ⟨(σ.set "__BranchTaken" (.bool false)).set "SEE" (.bits 128 651),
      fun o => ⟨fun h => ?_, fun h => ?_⟩, by frame_end⟩
    · by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact uartKvm_fwd_sp_zr hc httbr ha hs hn ht h
      · exact uartKvm_fwd_sp_r hc httbr ha hs hn ht h
      · exact uartKvm_fwd_x_zr hc httbr ha hs hn ht h
      · exact uartKvm_fwd_x_r hc httbr ha hs hn ht h
    · subst h
      by_cases hn : n.val = 31 <;> by_cases ht : t.val = 31
      · exact uartKvm_bwd_sp_zr hc httbr hd ha hs hn ht
      · exact uartKvm_bwd_sp_r hc httbr hd ha hs hn ht
      · exact uartKvm_bwd_x_zr hc httbr hd ha hs hn ht
      · exact uartKvm_bwd_x_r hc httbr hd ha hs hn ht

end TestSupport.A64.Isla

#print axioms TestSupport.A64.Isla.ldr_tcg
#print axioms TestSupport.A64.Isla.ldr_kvm
#print axioms TestSupport.A64.Isla.str_tcg
#print axioms TestSupport.A64.Isla.str_kvm
#print axioms TestSupport.A64.Isla.strb_tcg
#print axioms TestSupport.A64.Isla.strb_kvm
#print axioms TestSupport.A64.Isla.uart_tcg
#print axioms TestSupport.A64.Isla.uart_kvm
