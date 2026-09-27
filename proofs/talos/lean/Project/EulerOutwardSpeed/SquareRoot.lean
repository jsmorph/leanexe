import Project.EulerOutwardSpeed.Endpoint

namespace Project.EulerOutwardSpeed.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Order (finiteBits)
open Project.ProofKit.F64Outward (sqrt rejected)

theorem sqrt_exact (env : HostEnv Unit) (initial : Store Unit) (up : Bool) (a : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 34 initial
      [.i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧ values = checkedValues (sqrt up a)) := by
  refine TerminatesWith.of_wp_entry_for (f := func34Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func34 _ initial
    (func34Def.toLocals [.i64 (boolWord up), .i64 a]) env
  unfold func34
  wp_run [func34Def]
  refine wp_call_tw (finite_exact env initial a) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases ha : finiteBits a
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [sqrt, ha, checkedValues, rejected]
  · by_cases hn : a ≤ 0x8000000000000000
    · guard_peel
      guard_call (endpoint_exact env initial up (Wasm.IEEE64.sqrt a))
      simp [sqrt, ha, hn, checkedValues]
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [sqrt, ha, hn, checkedValues, rejected]

#print axioms sqrt_exact
end Project.EulerOutwardSpeed.Execution
