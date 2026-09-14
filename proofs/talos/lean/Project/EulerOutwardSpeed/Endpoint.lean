import Project.EulerOutwardSpeed.Adjacent

namespace Project.EulerOutwardSpeed.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Order (finiteBits)
open Project.ProofKit.F64Outward (Checked rejected neighbor endpoint)

def checkedValues (result : Checked) : List Value := [.i64 result.value, .i64 result.status]

theorem neighbor_exact (env : HostEnv Unit) (initial : Store Unit) (up : Bool) (bits : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 21 initial
      [.i64 bits, .i64 (boolWord up)]
      (fun final values => final = initial ∧ values = [.i64 (neighbor up bits)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func21Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func21 _ initial
    (func21Def.toLocals [.i64 (boolWord up), .i64 bits]) env
  unfold func21
  cases up <;> wp_run [func21Def, boolWord] <;> guard_peel
  · guard_call (nextDown_exact env initial bits)
    simp [neighbor]
  · guard_call (nextUp_exact env initial bits)
    simp [neighbor]

theorem endpoint_exact (env : HostEnv Unit) (initial : Store Unit) (up : Bool) (rounded : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 23 initial
      [.i64 rounded, .i64 (boolWord up)]
      (fun final values => final = initial ∧ values = checkedValues (endpoint up rounded)) := by
  refine TerminatesWith.of_wp_entry_for (f := func23Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func23 _ initial
    (func23Def.toLocals [.i64 (boolWord up), .i64 rounded]) env
  unfold func23
  wp_run [func23Def]
  refine wp_call_tw (finite_exact env initial rounded) ?_
  rintro st values ⟨hst, rfl⟩
  subst st
  cases hf : finiteBits rounded
  · guard_peel
    guard_call (rejected_exact env initial)
    simp [endpoint, hf, checkedValues, rejected]
  · guard_peel
    guard_call (neighbor_exact env initial up rounded)
    refine wp_call_tw (finite_exact env initial (neighbor up rounded)) ?_
    rintro st values ⟨hst, rfl⟩
    subst st
    cases he : finiteBits (neighbor up rounded)
    · guard_peel
      guard_call (rejected_exact env initial)
      simp [endpoint, hf, he, checkedValues, rejected]
    · guard_peel
      simp [endpoint, hf, he, checkedValues]

#print axioms neighbor_exact
#print axioms endpoint_exact
end Project.EulerOutwardSpeed.Execution
