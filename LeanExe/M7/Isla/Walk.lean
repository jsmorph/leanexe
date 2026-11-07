import LeanExe.M7.Isla.Check
import LeanExe.M7.Isla.Profile
import LeanExe.A64.Isla.Walk

/-!
The walk of the traces of the Cortex-M7 model's branches, loads, and stores, which the modules
`Branch` and `Memory` of `tests/TestSupport/M7/Isla` share.  `m7_fwd` and `m7_bwd` are `t32_fwd` and
`t32_bwd` of `LeanExe/M7/Isla/Check.lean` with the order of their rules changed: they take apart a
conjunction, an existential, a disjunction, or an `if` at the top of a path's hypothesis or goal
before they unfold its next event, and they evaluate the event again after taking an `if` inside it,
such as that of a write of `_PC`.  `t32_fwd` unfolds first, and its rewrite reaches the events under
a conjunction, so in a trace whose decode clauses fork, as those of the branches do, the hypothesis
of a path collects every branch of the fork as one formula, and `omega` in the discharger
case-splits its disjunctions until the job runs out of memory.  At a disjunction, `m7_bwd` takes the
branch whose first condition the tactic after `using` proves or `m7_simp` makes true.

The reset constraint of a load or store names `R0` to `R7` and the opcode's field `Rn`, and its
`ite` over the eight registers evaluates to the chain that `chain8_eq` folds into the indexed
register.  The address translation computes with the masks of `LeanExe/A64/Isla/Walk.lean` and
`and_fffff000000000`, and a read of the 8-byte descriptor is never a device access.
-/

namespace LeanExe.M7.Isla

open LeanExe.A64.Isla (Val)

/-- `t32_simp` with `mem_omega` of `LeanExe/A64/Isla/Walk.lean` as the discharger: `omega` without
the facts that a walk introduces, which have inaccessible names.  The conditions of the rules
follow from the theorem's facts, and with the walk's facts in its context, many of them
disequalities of the decode, `omega` slows down until the job runs out of time. -/
syntax "m7_simp " "[" Lean.Parser.Tactic.simpLemma,* "]" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| m7_simp [$xs,*] $(loc)?) => `(tactic|
    simp -failIfUnchanged (disch := mem_omega) only [
      eval, LeanExe.A64.Isla.Base.eval, LeanExe.A64.Isla.RVal.eval,
      LeanExe.A64.Isla.Base.evalAll, LeanExe.A64.Isla.Base.evalFields,
      LeanExe.A64.Isla.Unop.apply, LeanExe.A64.Isla.Binop.apply, LeanExe.A64.Isla.Binop.arith,
      LeanExe.A64.Isla.lshr, regGet, regSet, part, gprs, partGet, partPut, LeanExe.A64.Isla.bit,
      LeanExe.A64.Isla.acc, LeanExe.A64.Isla.upd, gprVals, runSome,
      LeanExe.A64.Isla.Vars.set_apply, LeanExe.A64.Isla.Sys.set_apply,
      LeanExe.A64.Isla.Sys.get_set, List.lookup,
      Option.bind, Option.map, Option.getD, LeanExe.A64.Isla.Val.bits.injEq,
      LeanExe.A64.Isla.Val.bool.injEq, LeanExe.A64.Isla.Val.enum.injEq,
      LeanExe.A64.Isla.Val.struct.injEq, LeanExe.A64.Isla.Val.vec.injEq, Option.some.injEq,
      Prod.mk.injEq, List.cons.injEq, List.map_cons, List.map_nil, List.cons_append,
      List.nil_append, eq_self_iff_true, decide_eq_true_eq, decide_eq_false_iff_not,
      Bool.not_eq_true', Bool.not_not, Bool.not_true, Bool.not_false, Bool.and_true,
      Bool.true_and, Bool.and_false, Bool.false_and, Bool.or_true, Bool.true_or, Bool.or_false,
      Bool.false_or, and_true, true_and, and_self, ne_eq, not_true_eq_false, not_false_eq_true,
      false_and, and_false, or_false, false_or, Nat.pow_zero, Nat.div_one, Nat.mod_mod,
      Nat.zero_add, LeanExe.A64.Isla.nat_add_zero, Nat.zero_mul, bit_div, bit_mod,
      LeanExe.A64.Isla.fin_mod, LeanExe.A64.Isla.fin_div, regAt_lt,
      setRegAt_lt, Fin.is_lt, ↓reduceIte,
      ↓reduceDIte, reduceCtorEq, String.reduceEq, String.reduceNe, String.reduceBEq,
      String.reduceAppend, String.reduceToList, Char.reduceBEq, Nat.reduceAdd, Nat.reduceSub,
      Nat.reduceMul, Nat.reduceDiv, Nat.reduceMod, Nat.reducePow, Nat.reduceEqDiff,
      Nat.reduceLeDiff, Nat.reduceLT, Nat.reduceGT, Nat.reduceBEq, Bool.cond_true,
      Bool.cond_false, decide_true, decide_false, chain_eq, $xs,*] $(loc)?)

/-- Takes the hypothesis `h`, that a path of a trace ends in an outcome, through the trace, as
`t32_fwd` does, taking apart its conjunctions, existentials, and disjunctions before it unfolds the
next event. -/
syntax "m7_fwd " ident " using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| m7_fwd $h using $d with [$xs,*]) => `(tactic| repeat' (first
      | (guard_hyp $h : False; exact False.elim $h)
      | (guard_hyp $h : Or _ _; rcases $h:ident with $h:ident | $h:ident)
      | (guard_hyp $h : Exists _; obtain ⟨x, $h:ident⟩ := $h:ident)
      | (guard_hyp $h : And _ _
         obtain ⟨x, $h:ident⟩ := $h:ident
         first
           | subst x
           | (guard_hyp x : _ = Mach.x _ _
              rw [x] at $h:ident
              m7_simp [$xs,*] at $h:ident)
           | skip)
      | (guard_hyp $h : @Eq Outcome _ _; subst $h:ident)
      | (guard_hyp $h : ite _ _ _; rw [ite_eq_left] at $h:ident; rotate_left; ($d))
      | (rw [LeanExe.M7.Isla.run] at $h:ident; m7_simp [$xs,*] at $h:ident)
      | focus (rw [ite_eq_left] at $h:ident; rotate_left; ($d); m7_simp [$xs,*] at $h:ident)))

/-- Builds a path of a trace up to its next `declare-const` of a free variable or its end, as
`t32_walk` does, splitting a conjunction and taking an `if` before it unfolds the next event.  At
a disjunction it takes the left branch when its first event's condition is true by `m7_simp` or
by the tactic after `using`, and the right branch otherwise. -/
syntax "m7_walk_step " "using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" :
  tactic
macro_rules
  | `(tactic| m7_walk_step using $d with [$xs,*]) => `(tactic| first
      | (guard_target = Or _ _
         first
           | (apply Or.inl
              rw [LeanExe.M7.Isla.run]
              m7_simp [$xs,*]
              fail_if_success guard_target = False
              first
                | (guard_target = And _ _; refine ⟨by $d, ?_⟩)
                | guard_target = LeanExe.M7.Isla.run _ _ _ _ _ _ _ _)
           | apply Or.inr)
      | (guard_target = And _ _; apply And.intro; rotate_left)
      | (guard_target = ite _ _ _; rw [ite_eq_left]; rotate_left; ($d))
      | (rw [LeanExe.M7.Isla.run]; m7_simp [$xs,*])
      | focus (rw [ite_eq_left]; rotate_left; ($d); m7_simp [$xs,*]))

/-- Repeats `m7_walk_step`: builds a path of a trace up to its next `declare-const` of a free
variable or its end. -/
syntax "m7_walk " "using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| m7_walk using $d with [$xs,*]) =>
    `(tactic| repeat (m7_walk_step using ($d) with [$xs,*]))

/-- Builds a path of a trace with `m7_walk`, giving the declared variables the values of the list
in order. -/
syntax "m7_bwd " "[" term,* "]" " using " tacticSeq " with "
  "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| m7_bwd [] using $d with [$xs,*]) => `(tactic| (m7_walk using ($d) with [$xs,*]))
  | `(tactic| m7_bwd [$w] using $d with [$xs,*]) => `(tactic| (
      m7_walk using ($d) with [$xs,*]
      guard_target = Exists _
      refine ⟨$w, ?_⟩
      m7_walk using ($d) with [$xs,*]))
  | `(tactic| m7_bwd [$w, $ws,*] using $d with [$xs,*]) => `(tactic| (
      m7_walk using ($d) with [$xs,*]
      guard_target = Exists _
      refine ⟨$w, ?_⟩
      m7_bwd [$ws,*] using ($d) with [$xs,*]))

/-- The value of a read of `k` bytes at the address `v`, as the semantics checks it: the next device
value at a device address, and the bytes of memory elsewhere. -/
def memVal (P : Platform) (δ : Nat → UInt32) (m : Mach) (k : Nat) : Val → Option Val
  | .bits 64 y => some (.bits (8 * k)
      (if device P y k then (δ m.s.reads).toNat else LeanExe.A64.Isla.bytes m.mem (.ofNat y) k))
  | _ => none

section Meta

open Lean Meta Elab Tactic

/-- The value of a declared variable that the event `b` reads from the machine `m` and the registers
`σ`, with the variables `ρ`, the platform `P`, and the device values `δ`, as `witness` of
`LeanExe/A64/Isla/Walk.lean` gives it for the A64 semantics, or 0 or `false` when no event reads
it.  A free Boolean of the M7 traces chooses how a register write treats bits 63 to 32, and
`false` keeps them, the path to the outcome with the machine's high words. -/
def m7Witness (isBool : Bool) (b : Option LeanExe.A64.Isla.Bind) (P δ ρ m σ : Expr) :
    MetaM Expr := do
  let some b := b | return if isBool then mkConst ``Bool.false else mkNatLit 0
  let opt ← match b with
    | .reg assume r al path =>
      let get ← mkAppM ``LeanExe.M7.Isla.regGet #[m, σ, r, al]
      match path with
      | .inl q =>
        let q' ← if assume then pure q else
          match LeanExe.A64.Isla.strList? al with
          | some al' => pure (q.drop al'.length)
          | none => throwError "m7_wit: accessor path not a literal"
        mkAppM ``Option.bind #[get, ← mkAppM ``LeanExe.A64.Isla.acc #[toExpr q']]
      | .inr j => mkAppM ``Option.bind #[get, ← mkAppM ``LeanExe.A64.Isla.vecAt #[mkNatLit j]]
    | .mem a k =>
      mkAppM ``Option.bind #[← mkAppM ``LeanExe.A64.Isla.Base.eval #[ρ, a],
        ← mkAppM ``memVal #[P, δ, m, k]]
    | .gpr j =>
      mkAppM ``GetElem?.getElem? #[← mkAppM ``LeanExe.M7.Isla.gprVals #[m], mkNatLit j]
    | .abs _ _ => throwError "m7_wit: an abstract call, which the M7 semantics does not interpret"
  mkAppM (if isBool then ``LeanExe.A64.Isla.witBool else ``LeanExe.A64.Isla.witBits) #[opt]

/-- Gives the variable that a goal
`∃ n, n < 2 ^ w ∧ run P δ len t (ρ.set x (.bits w n)) m σ o`, or
`∃ b, run P δ len t (ρ.set x (.bool b)) m σ o`, declares the value that the first event of `t`
reading it reads, as `mem_wit` of `LeanExe/A64/Isla/Walk.lean` does. -/
elab "m7_wit" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let_expr Exists ty p := tgt | throwError "m7_wit: not an existential"
  let .lam _ _ body _ := p | throwError "m7_wit: not a lambda"
  let r := if body.isAppOfArity ``And 2 then body.appArg! else body
  unless r.isAppOfArity ``LeanExe.M7.Isla.run 8 do throwError "m7_wit: not a path"
  let args := r.getAppArgs
  let ρ' := args[4]!
  unless ρ'.isAppOfArity ``LeanExe.A64.Isla.Vars.set 3 do throwError "m7_wit: no declaration"
  let ρ := ρ'.appFn!.appFn!.appArg!
  let some x := ρ'.appFn!.appArg!.nat? | throwError "m7_wit: variable not a literal"
  if ρ.hasLooseBVars || args[5]!.hasLooseBVars || args[6]!.hasLooseBVars then
    throwError "m7_wit: the machine depends on the witness"
  let w ← m7Witness (ty.isConstOf ``Bool) (← LeanExe.A64.Isla.findBind x args[3]!) args[0]!
    args[1]! ρ args[5]! args[6]!
  let stx ← Term.exprToSyntax w
  evalTactic (← `(tactic| refine ⟨$stx, ?_⟩))

end Meta

/-- Builds a path of a trace to its end with `m7_walk_step`, giving each declared variable, through
`m7_wit`, the value that the first event reading it reads, and evaluating that value at once, so
that the bound that the declaration asserts and every later read see the value. -/
syntax "m7_auto " "using " tacticSeq " with " "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| m7_auto using $d with [$xs,*]) => `(tactic| repeat (first
      | (guard_target = Exists _
         m7_wit
         m7_simp [LeanExe.A64.Isla.witBits, LeanExe.A64.Isla.witBool, LeanExe.A64.Isla.vecAt,
           memVal, List.getElem?_cons, $xs,*])
      | m7_walk_step using ($d) with [LeanExe.A64.Isla.witBits, LeanExe.A64.Isla.witBool,
          LeanExe.A64.Isla.vecAt, memVal, List.getElem?_cons, $xs,*]))

/-- `cond (decide (k = 7)) (m.x 7) (... (m.x 0))`, the chain of the reset constraint's `ite` over
`R0` to `R7` at the index `k`, as `m7_simp` writes it. -/
syntax "chain8% " term:max term:max : term
macro_rules
  | `(chain8% $m $k) => do
    let mut t ← `(Mach.x $m 0)
    for j in [1:8] do
      let lit := Lean.Syntax.mkNumLit (toString j)
      t ← `(cond (decide ($k = $lit)) (Mach.x $m $lit) $t)
    return t

/-- The chain at an index below 8 is that X register. -/
theorem chain8_eq {m : Mach} {k : Nat} (hk : k < 8) : chain8% m k = m.x k :=
  LeanExe.A64.Isla.pick_eq k (Mach.x m) 7 (by omega)

/-- `cond (decide (k = j + 7)) (f (j + 7)) (... (cond (decide (k = 8)) (f 8) b))`: the chain of a
read at the index `k` over the registers from 8, above the value `b`. -/
def pickFrom (k : Nat) (f : Nat → Nat) (b : Nat) : Nat → Nat
  | 0 => b
  | j + 1 => cond (decide (k = j + 8)) (f (j + 8)) (pickFrom k f b j)

theorem pickFrom_eq (k : Nat) (f : Nat → Nat) : ∀ j, pickFrom k f (f k) j = f k
  | 0 => rfl
  | j + 1 => by
    unfold pickFrom
    by_cases h : k = j + 8
    · subst h
      simp only [decide_true, Bool.cond_true]
    · simp only [h, decide_false, Bool.cond_false, pickFrom_eq k f j]

/-- The chain of a read at the index `k` from the X registers, as `m7_simp` writes it after
`chain8_eq` folds its part over `R0` to `R7`: `cond (decide (k = 30)) (m.x 30) (... (cond
(decide (k = 8)) (m.x 8) (m.x k)))`. -/
syntax "chain23% " term:max term:max : term
macro_rules
  | `(chain23% $m $k) => do
    let mut t ← `(Mach.x $m $k)
    for j in [8:31] do
      let lit := Lean.Syntax.mkNumLit (toString j)
      t ← `(cond (decide ($k = $lit)) (Mach.x $m $lit) $t)
    return t

/-- The chain of `chain23%` is the indexed register for every index. -/
theorem chain23_eq {m : Mach} {k : Nat} : chain23% m k = m.x k :=
  pickFrom_eq k (Mach.x m) 23

/-- A read of 8 bytes, such as the walk's read of a descriptor, is never a device access. -/
theorem device_eight (P : Platform) (y : Nat) : device P y 8 = false := rfl

/-- The mask of bits 55 to 36 of a physical address, which the walk tests against the supported
size of 44 bits. -/
theorem and_fffff000000000 {x : Nat} (h : x < 68719476736) : x &&& 72057525318451200 = 0 :=
  LeanExe.A64.Isla.and_hi_zero (c := 1048575) (k := 36) h

end LeanExe.M7.Isla
