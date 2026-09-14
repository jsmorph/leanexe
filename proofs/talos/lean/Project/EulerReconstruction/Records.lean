import Project.EulerReconstruction.Scalars

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerConservative.Execution (boolWord)
open Project.EulerRiemann.Reconstruction
open Project.ProofKit.F64Order (finiteBits)

macro "reconstruction_call" call:term : tactic => `(tactic|
  (refine wp_call_tw $call ?_
   rintro st values ⟨hst, hvalues⟩
   simp only [stateValues, facesValues, slopeValues] at hvalues
   subst st
   subst values
   guard_peel))

theorem admissible_exact (env : HostEnv Unit) (initial : Store Unit) (state : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 23 initial (stateValues state)
      (fun final values => final = initial ∧ values = [.i64 (boolWord (admissibleState state))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func23Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func23 _ initial
    (func23Def.toLocals [.i64 state.density, .i64 state.mx, .i64 state.my, .i64 state.energy]) env
  unfold func23
  wp_run [func23Def]
  guard_peel
  guard_call (state_guard_exact env initial state.density state.mx state.my state.energy)
  cases h : Project.EulerRiemann.Numerics.stateGuard
    state.density state.mx state.my state.energy <;>
    simp [admissibleState, stateValues, h]

theorem finite_state_exact (env : HostEnv Unit) (initial : Store Unit) (state : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 25 initial (stateValues state)
      (fun final values => final = initial ∧ values = [.i64 (boolWord (finiteState state))]) := by
  refine TerminatesWith.of_wp_entry_for (f := func25Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func25 _ initial
    (func25Def.toLocals [.i64 state.density, .i64 state.mx, .i64 state.my, .i64 state.energy]) env
  unfold func25
  wp_run [func25Def]
  guard_peel
  cases hr : finiteBits state.density
  all_goals guard_call (finite_exact env initial state.density)
  · simp [finiteState, hr, stateValues]
  · cases hx : finiteBits state.mx
    all_goals guard_call (finite_exact env initial state.mx)
    · simp [finiteState, hr, hx, stateValues]
    · cases hy : finiteBits state.my
      all_goals guard_call (finite_exact env initial state.my)
      · simp [finiteState, hr, hx, hy, stateValues]
      · cases he : finiteBits state.energy
        all_goals guard_call (finite_exact env initial state.energy)
        all_goals simp [finiteState, hr, hx, hy, he, stateValues]

theorem rejected_slope_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerReconstruction.«module» 29 initial []
      (fun final values => final = initial ∧ values = slopeValues rejectedSlope) := by
  refine TerminatesWith.of_wp_entry_for (f := func29Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func29 _ initial (func29Def.toLocals []) env
  unfold func29
  wp_run [func29Def]
  guard_peel
  reconstruction_call (zero_exact env initial)
  simp [slopeValues, rejectedSlope]

theorem rejected_faces_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerReconstruction.«module» 35 initial []
      (fun final values => final = initial ∧ values = facesValues rejectedFaces) := by
  refine TerminatesWith.of_wp_entry_for (f := func35Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func35 _ initial (func35Def.toLocals []) env
  unfold func35
  wp_run [func35Def]
  guard_peel
  reconstruction_call (zero_exact env initial)
  reconstruction_call (zero_exact env initial)
  simp [facesValues, rejectedFaces]

#print axioms admissible_exact
#print axioms finite_state_exact
#print axioms rejected_slope_exact
#print axioms rejected_faces_exact

end Project.EulerReconstruction.Execution
