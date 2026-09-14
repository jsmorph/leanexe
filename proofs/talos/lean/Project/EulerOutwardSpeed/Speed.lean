import Project.EulerOutwardSpeed.Thermodynamics

namespace Project.EulerOutwardSpeed.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Order (absBits)
open Project.ProofKit.F64Outward (div rejected)
open Project.EulerRiemann.OutwardSpeed

theorem speed_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 36 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = checkedValues (speedUpper rho mx my energy)) := by
  refine TerminatesWith.of_wp_entry_for (f := func36Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func36 _ initial
    (func36Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func36
  wp_run [func36Def]
  cases hg : Project.EulerRiemann.Numerics.stateGuard rho mx my energy
  all_goals guard_call (state_guard_exact env initial rho mx my energy)
  · guard_call (rejected_exact env initial)
    simp [speedUpper, hg, checkedValues, rejected]
  · guard_call (abs_exact env initial mx)
    outward_call (div_exact env initial true (absBits mx) rho)
    by_cases hv : (div true (absBits mx) rho).status = 0
    · by_cases hs : (soundUpper rho mx my energy).status = 0
      all_goals outward_call (sound_exact env initial rho mx my energy)
      · outward_call (add_exact env initial true (div true (absBits mx) rho).value
          (soundUpper rho mx my energy).value)
        simp [speedUpper, hg, hv, hs, checkedValues]
      · guard_call (rejected_exact env initial)
        simp [speedUpper, hg, hv, hs, checkedValues, rejected]
    · outward_call (sound_exact env initial rho mx my energy)
      guard_call (rejected_exact env initial)
      simp [speedUpper, hg, hv, checkedValues, rejected]

#print axioms speed_exact
end Project.EulerOutwardSpeed.Execution
