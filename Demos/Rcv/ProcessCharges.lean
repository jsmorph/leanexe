import Demos.Rcv.ProcessSizes
import Verified.Wasi.ResourceRules

/-! The allocation charges of the compiled process's `begin` and steps.  `begin` allocates nothing.
A write step allocates the remaining output and copies the state, and a stopping step copies the
state.  A read step allocates the read buffer and then copies the state at an errno, calls
`tabulate` on the input at EOF, or appends the bytes read to the input and copies the report.  The
charge of a read step holds for every reply of at most 4,096 bytes.  The WASI compilation's bound of
`tabulate` is the bound of `Demos.Rcv.TabulateProgram.compiled`, definitionally
(`tabulate_bound_eq`), so `TabulateProgram.tabulate_bound` closes it. -/

namespace Demos.Rcv.Process

open _root_.Verified _root_.Verified.Wasi _root_.Verified.Wasi.Resource
open LeanExe LeanExe.Wasi
open Demos.StreamFold (StreamPosition)

/-- The two compilations of `tabulate` have the same bound. -/
theorem tabulate_bound_eq (b : Bytes) :
    io.pureSources.tabulate.bound b = TabulateProgram.compiled.tabulate.bound b := rfl

theorem copyCost_bytes (b : Bytes) : Ty.bytes.copyCost b = Bytes.allocationCost b.data.size := by
  simp [Ty.copyCost]

theorem remainingOutput_bound_le (s : State) (pending : s.written < s.output.size) :
    io.pureSources.remainingOutput.bound s ≤ Bytes.allocationCost s.output.data.size := by
  rw [io.pureSources.remainingOutput.bound_eq]
  apply allocationCost_mono
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt pending)]
  have size : s.output.size.toNat ≤ s.output.data.size := by
    simp only [LeanExe.Bytes.size, UInt64.toNat_ofNat']
    exact Nat.mod_le _ _
  omega

theorem afterWrite_bound_le (s : State) (reply : WriteResult) :
    io.pureSources.afterWrite.bound (s, reply) ≤ stateTy.copyCost (sourceState s) := by
  rw [io.pureSources.afterWrite.bound_eq, state_copyCost]
  simp only [LeanExe.Pipeline.Flat.flat, copyCost_bytes, copyBytes]
  split
  · omega
  · split <;> omega

/-- The charge of `afterRead` from `s` for every reply: the copy of the state, the bound of
`tabulate` on the input, and the input extended by at most 4,096 bytes. -/
def afterReadCharge (s : State) : Nat :=
  copyBytes s + (80 * s.input.data.size + 33702909) +
    Bytes.allocationCost (s.input.data.size + 4096)

theorem afterRead_bound_le (s : State) (small : s.input.data.size < 2 ^ 32) (reply : ReadResult)
    (size : reply.bytes.data.size ≤ 4096) :
    io.pureSources.afterRead.bound (s, reply) ≤ afterReadCharge s := by
  have inputNat : s.input.size.toNat = s.input.data.size := Bytes.size_toNat s.input (by omega)
  have bytesNat : reply.bytes.size.toNat = reply.bytes.data.size :=
    Bytes.size_toNat reply.bytes (by omega)
  rw [io.pureSources.afterRead.bound_eq]
  simp only [LeanExe.Pipeline.Flat.flat, copyCost_bytes]
  unfold afterReadCharge copyBytes
  split
  · omega
  · split
    · have := TabulateProgram.tabulate_bound s.input small
      rw [tabulate_bound_eq]
      omega
    · rw [io.pureSources.append.bound_eq]
      have sum : (s.input.size + reply.bytes.size).toNat =
          s.input.data.size + reply.bytes.data.size := by
        rw [UInt64.toNat_add, inputNat, bytesNat]
        exact Nat.mod_eq_of_lt (by omega)
      rw [sum]
      have := allocationCost_mono (show s.input.data.size + reply.bytes.data.size ≤
        s.input.data.size + 4096 by omega)
      omega

/-- The charge of `begin`: `initial` allocates nothing. -/
def beginCharge : Nat := io.pureSources.initial.bound ()

theorem beginCharge_eq : beginCharge = 0 := io.pureSources.initial.bound_eq

section Bodies

local notation "pureContext" => Resource.PureContext.ofProg io.pure.program io.pure.funs

/-- Proves that a condition of an effect body has enough frames: it calls no function that takes
the call depth. -/
local macro "condition_fits" : tactic =>
  `(tactic| exact Expr.fits_of_depthCalls _ _ _ (by decide) _)

theorem stepModes : entryModes io.step.func.params io.step.func.modes = [.borrowed] := by
  decide

theorem readModes : entryModes io.readStep.func.params io.readStep.func.modes = [.borrowed] := by
  decide

theorem writeModes : entryModes io.writeStep.func.params io.writeStep.func.modes = [.borrowed] := by
  decide

/-- The charge of the write step from `s`: the remaining output and a copy of the state. -/
def writeCharge (s : State) : Nat :=
  io.pureSources.remainingOutput.bound s + stateTy.copyCost (sourceState s)

/-- The charge of the read step from `s`: the read buffer and the charge of `afterRead`. -/
def readCharge (s : State) : Nat :=
  Verified.Wasi.readCost 4096 + afterReadCharge s

/-- The charge of the step from `s` when no output remains: a copy of the state at EOF and a read
otherwise. -/
def restCharge (s : State) : Nat :=
  if s.eof = true then stateTy.copyCost (sourceState s) else readCharge s

/-- The charge of the step from `s`, by its branches. -/
def stepBudget (s : State) : Nat :=
  if s.written < s.output.size then writeCharge s else restCharge s

set_option maxHeartbeats 4000000 in
theorem writeStep_bounded {World : Type} (host : Host World) (depth : UInt64) (s : State) :
    Bounded host pureContext .nil depth
      (entryModes io.writeStep.func.params io.writeStep.func.modes) (fun _ => false)
      io.writeStep.func.body (.cons (sourceState s) .nil) (writeCharge s) := by
  rw [writeModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (io.pureSources.remainingOutput.bound s) (stateTy.copyCost (sourceState s))
    (Nat.le_refl _) ?_ ?_
  · apply bounded_of_rule
    intro spent fits rule
    refine rule (io.pureSources.remainingOutput.bound s) 0 (Nat.le_of_eq (Nat.add_zero _)) ?_ ?_
    · apply bounded_of_rule
      intro spent fits rule
      refine rule ?_ rfl
      simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
        Expr.allocs, Var.cost, Expr.mode, argsSum, callCredits, ↓reduceIte, Nat.add_zero,
        Nat.zero_add, coerceCost]
      show io.pureSources.remainingOutput.bound s ≤ _
      exact Nat.le_refl _
    · intro value _
      apply bounded_of_rule
      intro spent fits rule
      exact rule
  · intro value _
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp only [bindModes, ResultTy.bindEnv]
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, Expr.mode, argsSum, callCredits, Args.get_cons_zero', Args.get_cons_succ,
      Ty.copyCost_of_scalar, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
    show io.pureSources.afterWrite.bound (s, ⟨value.1, value.2⟩) ≤ _
    exact afterWrite_bound_le s _

set_option maxHeartbeats 4000000 in
theorem readStep_bounded {World : Type} (host : Host World) (depth : UInt64) {s : State}
    (small : s.input.data.size < 2 ^ 32) :
    Bounded host pureContext (.cons io.writeStep.func .nil) depth
      (entryModes io.readStep.func.params io.readStep.func.modes) (fun _ => false)
      io.readStep.func.body (.cons (sourceState s) .nil) (readCharge s) := by
  rw [readModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (Verified.Wasi.readCost 4096) _ (Nat.le_refl _) ?_ ?_
  · apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp +decide only [PureContext.readCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, ↓reduceIte, Nat.add_zero, Nat.zero_add]
    show Verified.Wasi.readCost 4096 ≤ _
    exact Nat.le_refl _
  · intro value returns
    have size : value.2.data.size ≤ 4096 := Returns.read_size returns
    apply bounded_of_rule
    intro spent fits rule
    refine rule ?_ rfl
    simp only [bindModes, ResultTy.bindEnv]
    simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg, Expr.allocs,
      Var.cost, Expr.mode, argsSum, callCredits, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
    show io.pureSources.afterRead.bound (s, ⟨value.1, value.2⟩) ≤ _
    exact afterRead_bound_le s small ⟨value.1, value.2⟩ size

set_option maxHeartbeats 4000000 in
theorem step_body_bounded {World : Type} (host : Host World) {s : State}
    (small : s.input.data.size < 2 ^ 32) :
    Bounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil)) 0
      (entryModes io.step.func.params io.step.func.modes) (fun _ => false) io.step.func.body
      (.cons (sourceState s) .nil) (stepBudget s) := by
  rw [stepModes]
  apply bounded_of_rule
  intro spent fits rule
  refine rule (writeCharge s) (restCharge s) ?_ rfl ?_ ?_
  · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost, ↓reduceIte,
      Nat.add_zero, Nat.zero_add]
    show (if decide (s.written < s.output.size) = true then writeCharge s
      else restCharge s) ≤ stepBudget s
    simp only [stepBudget, decide_eq_true_eq, Nat.le_refl]
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule (writeCharge s) ?_ rfl ?_
    · simp +decide only [PureContext.argumentCost, PureContext.exprCost, PureContext.ofProg,
        argsSum, ↓reduceIte, Nat.add_zero, Nat.zero_add]
      exact Nat.le_refl _
    · show CallBounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil))
        (.there .here) (0 + 1) (.cons (sourceState s) .nil) (writeCharge s)
      exact callBounded_there (callBounded_here (by decide) (writeStep_bounded host _ s))
  · intro _
    apply bounded_of_rule
    intro spent fits rule
    refine rule (stateTy.copyCost (sourceState s)) (readCharge s) ?_ (by condition_fits) ?_ ?_
    · simp +decide only [PureContext.exprCost, PureContext.ofProg, Expr.allocs, Var.cost,
        ↓reduceIte, Nat.add_zero, Nat.zero_add, ite_self, coerceCost]
      show (if (if s.eof = true then true else !true) = true then stateTy.copyCost (sourceState s)
        else readCharge s) ≤ restCharge s
      by_cases eof : s.eof = true <;> simp [eof, restCharge]
    · intro _
      apply bounded_of_rule
      intro spent fits rule
      refine rule ?_ rfl
      simp +decide only [PureContext.ownedCost, PureContext.exprCost, PureContext.ofProg,
        Expr.allocs, Var.cost, ↓reduceIte, Nat.add_zero, Nat.zero_add, coerceCost]
      show Ty.copyCost (.pair .bool (.pair .word stateTy)) (false, 0, sourceState s) ≤ _
      simp only [Ty.copyCost, Nat.zero_add, Nat.le_refl]
    · intro _
      apply bounded_of_rule
      intro spent fits rule
      refine rule (readCharge s) ?_ rfl ?_
      · simp +decide only [PureContext.argumentCost, PureContext.exprCost, PureContext.ofProg,
          argsSum, ↓reduceIte, Nat.add_zero, Nat.zero_add]
        exact Nat.le_refl _
      · show CallBounded host pureContext (.cons io.readStep.func (.cons io.writeStep.func .nil))
          .here (0 + 1) (.cons (sourceState s) .nil) (readCharge s)
        exact callBounded_here (by decide) (readStep_bounded host _ small)

/-- The step from `s` uses at most `stepBudget s` and has enough frames. -/
theorem step_bounded {World : Type} (host : Host World) {s : State}
    (small : s.input.data.size < 2 ^ 32) :
    CallBounded host pureContext io.program entry.step 0 (.cons (sourceState s) .nil)
      (stepBudget s) :=
  callBounded_there (callBounded_here (by decide) (step_body_bounded host small))

set_option maxHeartbeats 4000000 in
theorem begin_bounded {World : Type} (host : Host World) :
    CallBounded host pureContext io.program entry.begin 0 .nil beginCharge := by
  apply callBounded_here (by decide)
  apply bounded_of_rule
  intro spent fits rule
  refine rule ?_ rfl
  simp +decide only []

theorem begin_prefix_bound {World : Type} (host : Host World) (world : World) :
    CallPrefixBound host pureContext io.program entry.begin 0 .nil world beginCharge :=
  (begin_bounded host).2 world

end Bodies

/-- A bound on the charge of every step from a state with the sizes of `Sized L`: the copy of the
state, and for a read the buffer of 4,096 bytes, the bound of `tabulate` on `L` bytes, and the
input extended by 4,096 bytes. -/
def stepCharge (L : Nat) : Nat := copyLimit L + 81 * L + 33711204

theorem stepBudget_le {L : Nat} {s : State} (sized : Sized L s) : stepBudget s ≤ stepCharge L := by
  have copy := sized.copyCost
  have := sized.input
  have := sized.output
  have output := allocationCost_le s.output.data.size
  have extended := allocationCost_le (s.input.data.size + 4096)
  have readFull : Verified.Wasi.readCost 4096 = 4144 := by decide
  rw [state_copyCost] at copy
  unfold stepBudget restCharge
  split
  · rename_i pending
    have remaining := remainingOutput_bound_le s pending
    unfold writeCharge stepCharge
    rw [state_copyCost]
    simp only [copyLimit, outputLimit] at *
    omega
  · split
    · unfold stepCharge
      rw [state_copyCost]
      omega
    · unfold readCharge afterReadCharge stepCharge
      simp only [copyLimit] at *
      omega

/-- From a state with the sizes of `Sized L`, for `L` below `2 ^ 32`, the step uses at most
`stepCharge L`. -/
theorem step_prefix_bound {World : Type} (host : Host World) {L : Nat} (small : L < 2 ^ 32)
    {s : State} (sized : Sized L s) (world : World) :
    CallPrefixBound host (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program
      entry.step 0 (.cons (sourceState s) .nil) world (stepCharge L) :=
  ((step_bounded host (Nat.lt_of_le_of_lt sized.input small)).mono (stepBudget_le sized)).2 world

end Demos.Rcv.Process
