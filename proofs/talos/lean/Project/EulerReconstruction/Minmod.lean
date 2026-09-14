import Project.EulerReconstruction.Records

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction
open Project.ProofKit.F64Order (absBits)
open Project.ProofKit.F64Minmod (minmod)

theorem minmod_exact (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64) :
    TerminatesWith env Project.EulerReconstruction.«module» 26 initial [.i64 b, .i64 a]
      (fun final values => final = initial ∧ values = [.i64 (minmod a b)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func26Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func26 _ initial
    (func26Def.toLocals [.i64 a, .i64 b]) env
  unfold func26
  wp_run [func26Def]
  by_cases ha : a < 0x8000000000000000 <;>
    by_cases hb : b < 0x8000000000000000
  all_goals guard_peel
  · guard_call (abs_exact env initial a)
    by_cases hab : absBits a ≤ absBits b
    all_goals guard_tail_call ((abs_exact env initial b).append_args
      (f := func5Def) rfl rfl rfl [.i64 (absBits a)])
    all_goals simp [minmod, ha, hb, hab]
  · simp [minmod, ha, hb]
  · simp [minmod, ha, hb]
  · guard_call (abs_exact env initial a)
    by_cases hab : absBits a ≤ absBits b
    all_goals guard_tail_call ((abs_exact env initial b).append_args
      (f := func5Def) rfl rfl rfl [.i64 (absBits a)])
    all_goals simp [minmod, ha, hb, hab]

theorem minmod_state_exact (env : HostEnv Unit) (initial : Store Unit) (a b : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 27 initial
      (stateValues b ++ stateValues a)
      (fun final values => final = initial ∧ values = stateValues (minmodState a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func27Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func27 _ initial
    (func27Def.toLocals [.i64 a.density, .i64 a.mx, .i64 a.my, .i64 a.energy,
      .i64 b.density, .i64 b.mx, .i64 b.my, .i64 b.energy]) env
  unfold func27
  wp_run [func27Def]
  guard_peel
  guard_call (minmod_exact env initial a.density b.density)
  guard_call (minmod_exact env initial a.mx b.mx)
  guard_call (minmod_exact env initial a.my b.my)
  guard_call (minmod_exact env initial a.energy b.energy)
  simp [stateValues, minmodState]

#print axioms minmod_exact
#print axioms minmod_state_exact

end Project.EulerReconstruction.Execution
