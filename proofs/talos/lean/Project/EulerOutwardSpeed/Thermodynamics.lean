import Project.EulerOutwardSpeed.Kinetic
import Project.EulerOutwardSpeed.Subtraction
import Project.EulerOutwardSpeed.SquareRoot

namespace Project.EulerOutwardSpeed.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Outward (div rejected)
open Project.EulerRiemann.OutwardSpeed

theorem internal_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 31 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = checkedValues (internalUpper rho mx my energy)) := by
  refine TerminatesWith.of_wp_entry_for (f := func31Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func31 _ initial
    (func31Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func31
  wp_run [func31Def]
  by_cases hk : (kineticLower rho mx my).status = 0
  all_goals outward_call (kinetic_exact env initial rho mx my)
  · outward_call (sub_exact env initial true energy (kineticLower rho mx my).value)
    simp [internalUpper, hk, checkedValues]
  · guard_call (rejected_exact env initial)
    simp [internalUpper, hk, checkedValues, rejected]

theorem pressure_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 32 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = checkedValues (pressureUpper rho mx my energy)) := by
  refine TerminatesWith.of_wp_entry_for (f := func32Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func32 _ initial
    (func32Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func32
  wp_run [func32Def]
  by_cases hi : (internalUpper rho mx my energy).status = 0
  all_goals outward_call (internal_exact env initial rho mx my energy)
  · outward_call (mul_exact env initial true 0x3FD999999999999A
      (internalUpper rho mx my energy).value)
    simp [pressureUpper, hi, checkedValues]
  · guard_call (rejected_exact env initial)
    simp [pressureUpper, hi, checkedValues, rejected]

theorem radicand_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 33 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = checkedValues (radicandUpper rho mx my energy)) := by
  refine TerminatesWith.of_wp_entry_for (f := func33Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func33 _ initial
    (func33Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func33
  wp_run [func33Def]
  by_cases hp : (pressureUpper rho mx my energy).status = 0
  all_goals outward_call (pressure_exact env initial rho mx my energy)
  · by_cases hr : (div true (pressureUpper rho mx my energy).value rho).status = 0
    all_goals outward_call (div_exact env initial true (pressureUpper rho mx my energy).value rho)
    · outward_call (mul_exact env initial true 0x3FF6666666666667
        (div true (pressureUpper rho mx my energy).value rho).value)
      simp [radicandUpper, hp, hr, checkedValues]
    · guard_call (rejected_exact env initial)
      simp [radicandUpper, hp, hr, checkedValues, rejected]
  · guard_call (rejected_exact env initial)
    simp [radicandUpper, hp, checkedValues, rejected]

theorem sound_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 35 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧ values = checkedValues (soundUpper rho mx my energy)) := by
  refine TerminatesWith.of_wp_entry_for (f := func35Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func35 _ initial
    (func35Def.toLocals [.i64 rho, .i64 mx, .i64 my, .i64 energy]) env
  unfold func35
  wp_run [func35Def]
  by_cases hr : (radicandUpper rho mx my energy).status = 0
  all_goals outward_call (radicand_exact env initial rho mx my energy)
  · outward_call (sqrt_exact env initial true (radicandUpper rho mx my energy).value)
    simp [soundUpper, hr, checkedValues]
  · guard_call (rejected_exact env initial)
    simp [soundUpper, hr, checkedValues, rejected]

#print axioms internal_exact
#print axioms pressure_exact
#print axioms radicand_exact
#print axioms sound_exact
end Project.EulerOutwardSpeed.Execution
