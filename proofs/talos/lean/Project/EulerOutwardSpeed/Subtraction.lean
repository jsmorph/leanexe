import Project.EulerOutwardSpeed.Endpoint

namespace Project.EulerOutwardSpeed.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Order (finiteBits)
open Project.ProofKit.F64Outward (sub rejected)

theorem sub_exact (env : HostEnv Unit) (initial : Store Unit) (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 30 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧ values = checkedValues (sub up a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func30Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func30 _ initial
    (func30Def.toLocals [.i64 (boolWord up), .i64 a, .i64 b]) env
  unfold func30
  wp_run [func30Def]
  refine wp_call_tw (finite_exact env initial a) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases ha : finiteBits a
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [sub, ha, checkedValues, rejected]
  · guard_peel
    refine wp_call_tw (finite_exact env initial b) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases hb : finiteBits b
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [sub, ha, hb, checkedValues, rejected]
    · guard_peel
      guard_call (endpoint_exact env initial up (Wasm.IEEE64.sub a b))
      simp [sub, ha, hb, checkedValues]

#print axioms sub_exact
end Project.EulerOutwardSpeed.Execution
