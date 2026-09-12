import Project.EulerRiemann.ExecutionSide
import Project.EulerRiemann.ExecutionNeighbor
import Project.EulerRiemann.Time
import Project.ProofKit.CallRemainder

namespace Project.EulerRiemann.Execution
open Wasm

theorem endTime_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerRiemann.«module» 0 initial []
      (fun final values => final = initial ∧ values = [.i64 Time.endTime]) := by
  refine TerminatesWith.of_wp_entry_for (f := func0Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func0 _ initial (func0Def.toLocals []) env
  wp_run [func0Def, func0, Time.endTime]
  simp

theorem positiveBits_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 2 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.Euler2DConservative.Model.positiveBits word))]) :=
  Project.FunctionRegion.terminatesWith sideShift 0 (by norm_num [sideDomain])
    (Project.Euler2DConservative.Execution.positiveBits_exact
      Project.Euler2DConservative.Execution.concreteHelperLayout env initial word)

macro "time_guard_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func29Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        boolWord, f64Add, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem validAdvance_exact (env : HostEnv Unit) (initial : Store Unit) (time dt : UInt64) :
    TerminatesWith env Project.EulerRiemann.«module» 29 initial [.i64 dt, .i64 time]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Time.validAdvance time dt))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func29Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func29 _ initial
    (func29Def.toLocals [.i64 time, .i64 dt]) env
  unfold func29
  time_guard_peel
  refine wp_call_tw (positiveBits_exact env initial dt) ?_
  rintro current values ⟨hCurrent, rfl⟩
  subst current
  cases hPositive : Project.Euler2DConservative.Model.positiveBits dt with
  | false =>
    time_guard_peel
    simp [Time.validAdvance, hPositive]
  | true =>
    by_cases hIncrease : time < Wasm.IEEE64.add time dt
    · time_guard_peel
      refine wp_call_tw ((endTime_exact env initial).append_args rfl rfl rfl
        [.i64 (Wasm.IEEE64.add time dt)]) ?_
      rintro current values ⟨out, rfl, hCurrent, rfl⟩
      subst current
      by_cases hEnd : Wasm.IEEE64.add time dt ≤ Time.endTime <;>
        time_guard_peel <;>
        simp [Time.validAdvance, hPositive, hIncrease, hEnd]
    · time_guard_peel
      simp [Time.validAdvance, hPositive, hIncrease]

#print axioms endTime_exact
#print axioms positiveBits_exact
#print axioms validAdvance_exact

end Project.EulerRiemann.Execution
