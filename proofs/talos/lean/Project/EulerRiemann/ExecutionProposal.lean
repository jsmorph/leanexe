import Project.EulerRiemann.ExecutionSpacing

namespace Project.EulerRiemann.Execution
open Wasm

macro "proposal_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func28Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        f64Mul, f64Div, f64Sub, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine wp_iff_cons rfl ?_
      simp [*, -UInt64.not_le])

theorem proposal_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (time alpha : UInt64) (hn : n ≤ 800) :
    TerminatesWith env Project.EulerRiemann.«module» 28 initial
      [.i64 alpha, .i64 time, .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = [.i64 (Time.proposal n time alpha)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func28Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func28 _ initial
    (func28Def.toLocals [.i64 (UInt64.ofNat n), .i64 time, .i64 alpha]) env
  unfold func28
  proposal_peel
  refine wp_call_tw ((spacing_exact env initial n hn).append_args rfl rfl rfl
    [.f64 4600877379321698714]) ?_
  rintro current values ⟨out, rfl, hCurrent, rfl⟩
  subst current
  proposal_peel
  refine wp_call_tw ((endTime_exact env initial).append_args rfl rfl rfl
    [.i64 (IEEE64.div (IEEE64.mul 0x3FD999999999999A (Time.spacing n)) alpha)]) ?_
  rintro current values ⟨out, rfl, hCurrent, rfl⟩
  subst current
  by_cases hCompare : IEEE64.div (IEEE64.mul 0x3FD999999999999A (Time.spacing n)) alpha ≤
      IEEE64.sub Time.endTime time
  · proposal_peel
    refine wp_call_tw ((spacing_exact env initial n hn).append_args rfl rfl rfl
      [.f64 4600877379321698714]) ?_
    rintro current values ⟨out, rfl, hCurrent, rfl⟩
    subst current
    proposal_peel
    simp [Time.proposal, Min.min, hCompare]
  · proposal_peel
    refine wp_call_tw (endTime_exact env initial) ?_
    rintro current values ⟨hCurrent, rfl⟩
    subst current
    proposal_peel
    simp [Time.proposal, Min.min, hCompare]

#print axioms proposal_exact

end Project.EulerRiemann.Execution
