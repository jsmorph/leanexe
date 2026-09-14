import Project.EulerOutwardSpeed.Multiplication
import Project.EulerOutwardSpeed.Addition
import Project.EulerOutwardSpeed.Division
import Project.EulerRiemann.OutwardSpeed

namespace Project.EulerOutwardSpeed.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Outward (mul add div rejected)
open Project.EulerRiemann.OutwardSpeed (kineticLower)

macro "outward_call " call:term : tactic => `(tactic| (
  refine wp_call_tw $call ?_
  rintro st values ⟨hst, hvalues⟩
  simp only [checkedValues] at hvalues
  subst st
  subst values
  guard_peel))

theorem kinetic_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 29 initial
      [.i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = checkedValues (kineticLower rho mx my)) := by
  refine TerminatesWith.of_wp_entry_for (f := func29Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func29 _ initial
    (func29Def.toLocals [.i64 rho, .i64 mx, .i64 my]) env
  unfold func29
  wp_run [func29Def]
  outward_call (mul_exact env initial false mx mx)
  by_cases hx : (mul false mx mx).status = 0
  · by_cases hy : (mul false my my).status = 0
    · outward_call (mul_exact env initial false my my)
      by_cases hs : (add false (mul false mx mx).value (mul false my my).value).status = 0
      · outward_call (add_exact env initial false (mul false mx mx).value (mul false my my).value)
        by_cases hh : (mul false 0x3FE0000000000000
          (add false (mul false mx mx).value (mul false my my).value).value).status = 0
        · outward_call (mul_exact env initial false 0x3FE0000000000000
            (add false (mul false mx mx).value (mul false my my).value).value)
          outward_call (div_exact env initial false
            (mul false 0x3FE0000000000000
              (add false (mul false mx mx).value (mul false my my).value).value).value rho)
          simp [kineticLower, hx, hy, hs, hh, checkedValues]
        · outward_call (mul_exact env initial false 0x3FE0000000000000
            (add false (mul false mx mx).value (mul false my my).value).value)
          guard_call (rejected_exact env initial)
          simp [kineticLower, hx, hy, hs, hh, checkedValues, rejected]
      · outward_call (add_exact env initial false (mul false mx mx).value (mul false my my).value)
        guard_call (rejected_exact env initial)
        simp [kineticLower, hx, hy, hs, checkedValues, rejected]
    · outward_call (mul_exact env initial false my my)
      guard_call (rejected_exact env initial)
      simp [kineticLower, hx, hy, checkedValues, rejected]
  · outward_call (mul_exact env initial false my my)
    guard_call (rejected_exact env initial)
    simp [kineticLower, hx, checkedValues, rejected]

#print axioms kinetic_exact
end Project.EulerOutwardSpeed.Execution
