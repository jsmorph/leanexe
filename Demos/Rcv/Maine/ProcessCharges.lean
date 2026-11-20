import Demos.Rcv.Maine.ProcessFuture
import Demos.Rcv.Maine.ProcessProof
import Demos.Rcv.ProcessSizes
import Verified.Wasi.ResourceRules

/-! The allocation charges of the compiled Maine process's `begin` and steps.  `begin` allocates
the buffer of `readAll`, of `limit + 4,096` bytes, and then calls `tabulate` on an input of at most
`limit` bytes or builds a stopped state.  A step takes the state owned and allocates nothing: it
moves the state into the write step, whose write of the output's window allocates nothing and which
moves the state into `afterWrite`, or returns it.  The WASI compilation's bound of `tabulate` is the bound of
`Demos.Rcv.Maine.TabulateProgram.compiled`, definitionally (`tabulate_bound_eq`), so
`TabulateProgram.tabulate_bound` closes it.  A state whose output has at most `outputLimit` bytes,
as every state of a run has, costs at most `copyLimit` bytes to copy (`copyCost_le`). -/

namespace Demos.Rcv.Maine.Process

open _root_.Verified _root_.Verified.Wasi _root_.Verified.Wasi.Resource
open LeanExe LeanExe.Wasi
open Demos.Rcv.Process (State limit stateTy sourceState copyBytes state_copyCost copyCost_bytes
  limit_toNat)

/-- A bound on the copy of a state whose output has at most `outputLimit` bytes: a report block of
at most `outputLimit + 55` bytes. -/
def copyLimit : Nat := 1304229

theorem copyCost_le {s : State} (size : s.output.data.size ≤ outputLimit) :
    stateTy.copyCost (sourceState s) ≤ copyLimit := by
  rw [state_copyCost]
  have output := allocationCost_le s.output.data.size
  simp only [copyBytes, copyLimit, outputLimit] at *
  omega

/-! ## Charges -/

/-- The two compilations of `tabulate` have the same bound. -/
theorem tabulate_bound_eq (b : Bytes) :
    io.pureSources.tabulate.bound b = TabulateProgram.compiled.tabulate.bound b := rfl

/-- `afterWrite` takes the state owned and allocates nothing. -/
theorem afterWrite_bound (s : State) (reply : WriteResult) :
    io.pureSources.afterWrite.bound (⟨s⟩, reply) = 0 :=
  io.pureSources.afterWrite.bound_eq s reply

/-- The charge of `started`: the bound of `tabulate` on `limit` bytes. -/
def startedCharge : Nat := 80 * 50000000 + 33958029

theorem started_bound_le (input : ReadResult) (small : input.bytes.data.size < 2 ^ 32) :
    io.pureSources.started.bound input ≤ startedCharge := by
  have bytesNat : input.bytes.size.toNat = input.bytes.data.size :=
    Bytes.size_toNat input.bytes (by omega)
  rw [io.pureSources.started.bound_eq]
  unfold startedCharge
  split
  · omega
  · split
    · omega
    · rename_i within
      have sizeLe : input.bytes.data.size ≤ 50000000 := by
        rw [UInt64.lt_iff_toNat_lt, bytesNat, limit_toNat] at within
        omega
      have := TabulateProgram.tabulate_bound input.bytes small
      rw [tabulate_bound_eq]
      omega

/-- The charge of `begin`: the buffer of `readAll` and the charge of `started`. -/
def beginCharge : Nat := Verified.Wasi.readAllCost limit + startedCharge

theorem beginCharge_eq : beginCharge = 4083962173 := by
  decide

section Bodies

local notation "pureContext" => Resource.PureContext.ofProg io.pure.program io.pure.funs

theorem stepModes : entryModes io.step.func.params io.step.func.modes = [.owned] := by
  decide

theorem writeModes : entryModes io.writeStep.func.params io.writeStep.func.modes = [.owned] := by
  decide

set_option maxHeartbeats 4000000 in
/-- The write step allocates nothing: it moves the state into `afterWrite`, which takes it owned,
and the write of the output's window allocates nothing. -/
theorem writeStep_bounded {World : Type} (host : Host World) (depth : UInt64) (s : State) :
    Bounded host pureContext .nil depth
      (entryModes io.writeStep.func.params io.writeStep.func.modes) (fun _ => false)
      io.writeStep.func.body (.cons (sourceState s) .nil) 0 := by
  rw [writeModes]
  letPair_free
  apply bounded_of_rule
  intro spent fits rule
  refine rule 0 0 (Nat.le_refl _) ?_ ?_
  · repeat (first
      | (apply bounded_of_rule
         intro spent fits rule
         refine rule 0 0 (Nat.le_refl _) ?_ ?_)
      | (intro value _)
      | (apply bounded_of_rule
         intro spent fits rule
         exact rule)
      | (apply bounded_of_rule
         intro spent fits rule
         refine rule ?_ rfl
         simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
           Expr.allocs, Var.cost, Expr.mode, argsSum, callCredits, Ty.copyCost,
           Ty.copyCost_of_scalar, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]))
  · intro value _
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp only [bindModes, ResultTy.bindEnv]
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, Expr.mode, argsSum, callCredits, Args.get_cons_zero', Args.get_cons_succ,
      Ty.copyCost_of_scalar, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost,
      Expr.ownedCost, Var.ownedCost, modeAt, letPairModes, Mode.join, List.getD_cons_zero,
      List.getD_cons_succ, Var.index_ofIndex]
    show io.pureSources.afterWrite.bound (⟨s⟩, ⟨value.1, value.2⟩) ≤ 0
    rw [afterWrite_bound]

set_option maxHeartbeats 4000000 in
/-- The step allocates nothing: it moves the state into the write step, or returns it. -/
theorem step_body_bounded {World : Type} (host : Host World) (s : State) :
    Bounded host pureContext (.cons io.writeStep.func .nil) 0
      (entryModes io.step.func.params io.step.func.modes) (fun _ => false) io.step.func.body
      (.cons (sourceState s) .nil) 0 := by
  rw [stepModes]
  letPair_free
  apply bounded_of_rule
  intro spent fits rule
  refine rule 0 0 ?_ rfl ?_ ?_
  · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost, Ty.copyCost,
      ↓reduceIte, Nat.add_zero, Nat.zero_add]
    exact Nat.le_of_eq (ite_self _)
  · intro _
    refine Bounded.bind_ret (nextBudget := 0) ?_ rfl ?_
    · simp +decide only [PureContext.ownedCost, PureContext.exprCost,
        Expr.allocs, Var.cost, ↓reduceIte, Nat.add_zero, coerceCost, Nat.le_refl]
    apply bounded_of_rule
    intro spent fits rule
    refine rule 0 ?_ rfl ?_
    · exact Nat.le_trans (Nat.add_le_add_right (Nat.le_of_eq rfl) _)
        (Nat.le_of_eq (Nat.zero_add _))
    · show CallBounded host pureContext (.cons io.writeStep.func .nil)
        .here (0 + 1) (.cons (sourceState s) .nil) 0
      exact callBounded_here (by decide) (writeStep_bounded host _ s)
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
      Expr.allocs, Var.cost, Ty.copyCost, ↓reduceIte, Nat.add_zero, coerceCost, Nat.le_refl]

/-- The step from `s` allocates nothing and has enough frames. -/
theorem step_bounded {World : Type} (host : Host World) (s : State) :
    CallBounded host pureContext io.program entry.step 0 (.cons (sourceState s) .nil) 0 :=
  callBounded_there (callBounded_here (by decide) (step_body_bounded host s))

set_option maxHeartbeats 4000000 in
theorem begin_body_bounded {World : Type} (host : Host World) :
    Bounded host pureContext (.cons io.step.func (.cons io.writeStep.func .nil)) 0
      (entryModes io.begin.func.params io.begin.func.modes) (fun _ => false) io.begin.func.body
      .nil beginCharge := by
  apply bounded_of_rule
  intro spent fits rule
  refine rule (Verified.Wasi.readAllCost limit) startedCharge (Nat.le_refl _) ?_ ?_
  · apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    decide
  · intro value returns
    have size := Returns.readAll_size returns
    letPair_free
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp only [bindModes, ResultTy.bindEnv]
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, Expr.mode, argsSum, callCredits, ↓reduceIte, Nat.add_zero, Nat.zero_add,
      coerceCost]
    show io.pureSources.started.bound ⟨value.1, value.2⟩ ≤ _
    change value.2.data.size ≤ 50000000 + 4096 at size
    exact started_bound_le ⟨value.1, value.2⟩ (show value.2.data.size < 2 ^ 32 by omega)

theorem begin_bounded {World : Type} (host : Host World) :
    CallBounded host pureContext io.program entry.begin 0 .nil beginCharge :=
  callBounded_here (by decide) (begin_body_bounded host)

theorem begin_prefix_bound {World : Type} (host : Host World) (world : World) :
    CallPrefixBound host pureContext io.program entry.begin 0 .nil world beginCharge :=
  (begin_bounded host).2 world

end Bodies

/-- A bound on the charge of every step from a state whose output has at most `outputLimit`
bytes. -/
def stepCharge : Nat := 2 * copyLimit

/-- From a state whose output has at most `outputLimit` bytes, the step uses at most
`stepCharge`. -/
theorem step_prefix_bound {World : Type} (host : Host World) {s : State}
    (_size : s.output.data.size ≤ outputLimit) (world : World) :
    CallPrefixBound host (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program
      entry.step 0 (.cons (sourceState s) .nil) world stepCharge :=
  ((step_bounded host s).mono (Nat.zero_le _)).2 world

end Demos.Rcv.Maine.Process
