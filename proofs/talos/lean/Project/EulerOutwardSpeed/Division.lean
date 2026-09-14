import Project.EulerOutwardSpeed.Endpoint

namespace Project.EulerOutwardSpeed.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Order (finiteBits absBits)
open Project.ProofKit.F64Outward (div rejected)

theorem div_exact (env : HostEnv Unit) (initial : Store Unit) (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 24 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧ values = checkedValues (div up a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func24 _ initial
    (func24Def.toLocals [.i64 (boolWord up), .i64 a, .i64 b]) env
  unfold func24
  wp_run [func24Def]
  refine wp_call_tw (finite_exact env initial a) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases ha : finiteBits a
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [div, ha, checkedValues, rejected]
  · guard_peel
    refine wp_call_tw (finite_exact env initial b) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases hb : finiteBits b
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [div, ha, hb, checkedValues, rejected]
    · guard_peel
      by_cases hn : 0 < absBits b
      all_goals guard_tail_call ((abs_exact env initial b).append_args
        (f := func5Def) rfl rfl rfl [.i64 0])
      ·
        guard_call (endpoint_exact env initial up (Wasm.IEEE64.div a b))
        simp [div, ha, hb, hn, checkedValues]
      ·
        guard_call (rejected_exact env initial)
        simp [div, ha, hb, hn, checkedValues, rejected]

#print axioms div_exact
end Project.EulerOutwardSpeed.Execution
