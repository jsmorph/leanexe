import Demos.Rcv.ProcessProof
import Demos.Rcv.ProcessSizes
import Verified.Wasi.ResourceRules

/-! The allocation charges of the compiled process's `begin` and steps.  `begin` allocates the
buffer of `readAll`, of `limit + 4,096` bytes, and then calls `tabulate` on an input of at most
`limit` bytes or builds a stopped state.  `started` takes the result of `readAll` owned, which
`begin` moves into it.  A write step allocates the remaining output and copies the state at its
call of `afterWrite`, which takes the state owned, and a stopping step copies the state.  The WASI
compilation's bound of `tabulate` is the bound of `Demos.Rcv.TabulateProgram.compiled`,
definitionally (`tabulate_bound_eq`), so `TabulateProgram.tabulate_bound` closes it. -/

namespace Demos.Rcv.Process

open _root_.Verified _root_.Verified.Wasi _root_.Verified.Wasi.Resource
open LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamPosition)

/-- The two compilations of `tabulate` have the same bound. -/
theorem tabulate_bound_eq (b : Bytes) :
    io.pureSources.tabulate.bound b = TabulateProgram.compiled.tabulate.bound b := rfl

/-- `afterWrite` takes the state owned and allocates nothing. -/
theorem afterWrite_bound (s : State) (reply : WriteResult) :
    io.pureSources.afterWrite.bound (⟨s⟩, reply) = 0 :=
  io.pureSources.afterWrite.bound_eq s reply

/-- The charge of `started`: the bound of `tabulate` on `limit` bytes. -/
def startedCharge : Nat := 80 * 50000000 + 33702909

theorem started_bound_le (input : ReadResult) (small : input.bytes.data.size < 2 ^ 32) :
    io.pureSources.started.bound ⟨input⟩ ≤ startedCharge := by
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

theorem beginCharge_eq : beginCharge = 4083707053 := by
  decide

section Bodies

local notation "pureContext" => Resource.PureContext.ofProg io.pure.program io.pure.funs

theorem stepModes : entryModes io.step.func.params io.step.func.modes = [.borrowed] := by
  decide

theorem writeModes : entryModes io.writeStep.func.params io.writeStep.func.modes = [.borrowed] := by
  decide

/-- The charge of the write step from `s`: a copy of the state.  The write of the output's
window allocates nothing. -/
def writeCharge (s : State) : Nat :=
  stateTy.copyCost (sourceState s)

/-- The charge of the step from `s`, by its branches. -/
def stepBudget (s : State) : Nat :=
  if s.written < s.output.size then writeCharge s else stateTy.copyCost (sourceState s)

set_option maxHeartbeats 4000000 in
theorem writeStep_bounded {World : Type} (host : Host World) (depth : UInt64) (s : State) :
    Bounded host pureContext .nil depth
      (entryModes io.writeStep.func.params io.writeStep.func.modes) (fun _ => false)
      io.writeStep.func.body (.cons (sourceState s) .nil) (writeCharge s) := by
  rw [writeModes]
  letPair_free
  apply bounded_of_rule
  intro spent fits rule
  refine rule 0 (stateTy.copyCost (sourceState s)) (Nat.le_of_eq (Nat.zero_add _)) ?_ ?_
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
    show stateTy.copyCost (sourceState s) +
      io.pureSources.afterWrite.bound (⟨s⟩, ⟨value.1, value.2⟩) ≤ _
    rw [afterWrite_bound]
    exact Nat.le_of_eq (Nat.add_zero _)

set_option maxHeartbeats 4000000 in
theorem step_body_bounded {World : Type} (host : Host World) (s : State) :
    Bounded host pureContext (.cons io.writeStep.func .nil) 0
      (entryModes io.step.func.params io.step.func.modes) (fun _ => false) io.step.func.body
      (.cons (sourceState s) .nil) (stepBudget s) := by
  rw [stepModes]
  letPair_free
  apply bounded_of_rule
  intro spent fits rule
  refine rule (writeCharge s) (stateTy.copyCost (sourceState s)) ?_ rfl ?_ ?_
  · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost,
      ↓reduceIte, Nat.add_zero, Nat.zero_add]
    show (if decide (s.written < s.output.size) = true then writeCharge s
      else stateTy.copyCost (sourceState s)) ≤ stepBudget s
    simp only [stepBudget, decide_eq_true_eq, Nat.le_refl]
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule (writeCharge s) ?_ rfl ?_
    · simp +decide only [PureContext.argumentCost, PureContext.exprCost, PureContext.ofProg,
        argsSum, ↓reduceIte, Nat.add_zero, Nat.zero_add]
      exact Nat.le_refl _
    · show CallBounded host pureContext (.cons io.writeStep.func .nil)
        .here (0 + 1) (.cons (sourceState s) .nil) (writeCharge s)
      exact callBounded_here (by decide) (writeStep_bounded host _ s)
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
      Expr.allocs, Var.cost, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
    show Ty.copyCost (.pair .bool (.pair .word stateTy)) (false, 0, sourceState s) ≤ _
    simp only [Ty.copyCost, Nat.zero_add, Nat.le_refl]

/-- The step from `s` uses at most `stepBudget s` and has enough frames. -/
theorem step_bounded {World : Type} (host : Host World) (s : State) :
    CallBounded host pureContext io.program entry.step 0 (.cons (sourceState s) .nil)
      (stepBudget s) :=
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
      coerceCost, Expr.ownedCost, Var.ownedCost, modeAt, letPairModes, Mode.join,
      Args.get_cons_zero', Args.get_cons_succ, List.getD_cons_zero, List.getD_cons_succ,
      Var.index_ofIndex]
    show io.pureSources.started.bound ⟨⟨value.1, value.2⟩⟩ ≤ _
    change value.2.data.size ≤ 50000000 + 4096 at size
    exact started_bound_le ⟨value.1, value.2⟩ (show value.2.data.size < 2 ^ 32 by omega)

theorem begin_bounded {World : Type} (host : Host World) :
    CallBounded host pureContext io.program entry.begin 0 .nil beginCharge :=
  callBounded_here (by decide) (begin_body_bounded host)

theorem begin_prefix_bound {World : Type} (host : Host World) (world : World) :
    CallPrefixBound host pureContext io.program entry.begin 0 .nil world beginCharge :=
  (begin_bounded host).2 world

end Bodies

/-- A bound on the charge of every step from a state with the size of `Sized`: the remaining
output and the copy of the state. -/
def stepCharge : Nat := 2 * copyLimit

theorem stepBudget_le {s : State} (sized : Sized s) : stepBudget s ≤ stepCharge := by
  have copy := sized.copyCost
  have := sized.output
  have output := allocationCost_le s.output.data.size
  rw [state_copyCost] at copy
  unfold stepBudget
  split
  · rename_i pending
    unfold writeCharge stepCharge
    rw [state_copyCost]
    simp only [copyLimit, outputLimit] at *
    omega
  · unfold stepCharge
    rw [state_copyCost]
    omega

/-- From a state with the size of `Sized`, the step uses at most `stepCharge`. -/
theorem step_prefix_bound {World : Type} (host : Host World) {s : State} (sized : Sized s)
    (world : World) :
    CallPrefixBound host (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program
      entry.step 0 (.cons (sourceState s) .nil) world stepCharge :=
  ((step_bounded host s).mono (stepBudget_le sized)).2 world

end Demos.Rcv.Process
