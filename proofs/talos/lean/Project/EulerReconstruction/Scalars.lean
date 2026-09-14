import Project.EulerReconstruction.Guard
import Project.EulerRiemann.Reconstruction

namespace Project.EulerReconstruction.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerRiemann.Reconstruction

def stateValues (state : State) : List Value :=
  [.i64 state.energy, .i64 state.my, .i64 state.mx, .i64 state.density]

def facesValues (faces : Faces) : List Value :=
  [.i64 faces.factor, .i64 faces.right.energy, .i64 faces.right.my,
   .i64 faces.right.mx, .i64 faces.right.density, .i64 faces.left.energy,
   .i64 faces.left.my, .i64 faces.left.mx, .i64 faces.left.density, .i64 faces.status]

def slopeValues (slope : CheckedSlope) : List Value :=
  [.i64 slope.state.energy, .i64 slope.state.my, .i64 slope.state.mx,
   .i64 slope.state.density, .i64 slope.status]

theorem difference_exact (env : HostEnv Unit) (initial : Store Unit) (a b : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 24 initial
      (stateValues b ++ stateValues a)
      (fun final values => final = initial ∧ values = stateValues (difference a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func24 _ initial
    (func24Def.toLocals [.i64 a.density, .i64 a.mx, .i64 a.my, .i64 a.energy,
      .i64 b.density, .i64 b.mx, .i64 b.my, .i64 b.energy]) env
  unfold func24
  wp_run [func24Def, stateValues, difference]
  side_fp_peel
  simp

theorem sum_exact (env : HostEnv Unit) (initial : Store Unit) (a b : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 34 initial
      (stateValues b ++ stateValues a)
      (fun final values => final = initial ∧ values = stateValues (sum a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func34Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func34 _ initial
    (func34Def.toLocals [.i64 a.density, .i64 a.mx, .i64 a.my, .i64 a.energy,
      .i64 b.density, .i64 b.mx, .i64 b.my, .i64 b.energy]) env
  unfold func34
  wp_run [func34Def, stateValues, sum]
  side_fp_peel
  simp

theorem scale_exact (env : HostEnv Unit) (initial : Store Unit) (factor : UInt64) (state : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 33 initial
      (stateValues state ++ [.i64 factor])
      (fun final values => final = initial ∧ values = stateValues (scale factor state)) := by
  refine TerminatesWith.of_wp_entry_for (f := func33Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func33 _ initial
    (func33Def.toLocals [.i64 factor, .i64 state.density, .i64 state.mx,
      .i64 state.my, .i64 state.energy]) env
  unfold func33
  wp_run [func33Def, stateValues, scale]
  side_fp_peel
  simp

theorem zero_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerReconstruction.«module» 28 initial []
      (fun final values => final = initial ∧ values = stateValues zeroState) := by
  refine TerminatesWith.of_wp_entry_for (f := func28Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func28 _ initial (func28Def.toLocals []) env
  unfold func28
  wp_run [func28Def, stateValues, zeroState]
  guard_peel
  simp

theorem constant_exact (env : HostEnv Unit) (initial : Store Unit) (center : State) :
    TerminatesWith env Project.EulerReconstruction.«module» 32 initial (stateValues center)
      (fun final values => final = initial ∧ values = facesValues (constantFaces center)) := by
  refine TerminatesWith.of_wp_entry_for (f := func32Def) rfl ?_ (by decide)
  change wp Project.EulerReconstruction.«module» func32 _ initial
    (func32Def.toLocals [.i64 center.density, .i64 center.mx, .i64 center.my, .i64 center.energy]) env
  unfold func32
  wp_run [func32Def, facesValues, constantFaces]
  guard_peel
  simp [stateValues]

#print axioms difference_exact
#print axioms sum_exact
#print axioms scale_exact
#print axioms zero_exact
#print axioms constant_exact

end Project.EulerReconstruction.Execution
