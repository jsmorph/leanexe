import Project.EulerCertificate.IntervalExecution
import Project.EulerCertificate.Vectors

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerCertificate.Flux (Vector)
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerCertificateFlux.Execution (boundsValues vectorValues)
open Project.EulerConservative.Execution (boolWord)

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

theorem vector_zero_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerCertificate.«module» 67 initial []
      (fun final values => final = initial ∧ values = vectorValues Vectors.zero) := by
  refine TerminatesWith.of_wp_entry_for (f := func67Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func67 _ initial (func67Def.toLocals []) env
  unfold func67
  wp_run [func67Def, vectorValues, boundsValues, Vectors.zero]
  simp [List.set]

theorem vector_state_exact (env : HostEnv Unit) (initial : Store Unit) (q : State) :
    TerminatesWith env Project.EulerCertificate.«module» 72 initial
      [.i64 q.energy, .i64 q.my, .i64 q.mx, .i64 q.density]
      (fun final values => final = initial ∧ values = vectorValues (Vectors.state q)) := by
  refine TerminatesWith.of_wp_entry_for (f := func72Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func72 _ initial
    (func72Def.toLocals [.i64 q.density, .i64 q.mx, .i64 q.my, .i64 q.energy]) env
  unfold func72
  wp_run [func72Def]
  guard_call (interval_point_exact env initial q.density)
  guard_call (interval_point_exact env initial q.mx)
  guard_call (interval_point_exact env initial q.my)
  guard_call (interval_point_exact env initial q.energy)
  simp [Vectors.state, vectorValues, boundsValues]

theorem vector_add_exact (env : HostEnv Unit) (initial : Store Unit)
    (a b : Vector) :
    TerminatesWith env Project.EulerCertificate.«module» 70 initial
      (vectorValues b ++ vectorValues a)
      (fun final values => final = initial ∧ values = vectorValues (Vectors.add a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func70Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func70 _ initial
    (func70Def.toLocals [.i64 a.mass.status, .i64 a.mass.lower, .i64 a.mass.upper, .i64 a.momentum.status, .i64 a.momentum.lower, .i64 a.momentum.upper, .i64 a.transverse.status, .i64 a.transverse.lower, .i64 a.transverse.upper, .i64 a.energy.status, .i64 a.energy.lower, .i64 a.energy.upper, .i64 b.mass.status, .i64 b.mass.lower, .i64 b.mass.upper, .i64 b.momentum.status, .i64 b.momentum.lower, .i64 b.momentum.upper, .i64 b.transverse.status, .i64 b.transverse.lower, .i64 b.transverse.upper, .i64 b.energy.status, .i64 b.energy.lower, .i64 b.energy.upper]) env
  unfold func70
  wp_run [func70Def]
  guard_call (interval_add_exact env initial a.mass b.mass)
  guard_call (interval_add_exact env initial a.momentum b.momentum)
  guard_call (interval_add_exact env initial a.transverse b.transverse)
  guard_call (interval_add_exact env initial a.energy b.energy)
  simp [Vectors.add, vectorValues, boundsValues]

theorem vector_sub_exact (env : HostEnv Unit) (initial : Store Unit)
    (a b : Vector) :
    TerminatesWith env Project.EulerCertificate.«module» 171 initial
      (vectorValues b ++ vectorValues a)
      (fun final values => final = initial ∧ values = vectorValues (Vectors.sub a b)) := by
  refine TerminatesWith.of_wp_entry_for (f := func171Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func171 _ initial
    (func171Def.toLocals [.i64 a.mass.status, .i64 a.mass.lower, .i64 a.mass.upper, .i64 a.momentum.status, .i64 a.momentum.lower, .i64 a.momentum.upper, .i64 a.transverse.status, .i64 a.transverse.lower, .i64 a.transverse.upper, .i64 a.energy.status, .i64 a.energy.lower, .i64 a.energy.upper, .i64 b.mass.status, .i64 b.mass.lower, .i64 b.mass.upper, .i64 b.momentum.status, .i64 b.momentum.lower, .i64 b.momentum.upper, .i64 b.transverse.status, .i64 b.transverse.lower, .i64 b.transverse.upper, .i64 b.energy.status, .i64 b.energy.lower, .i64 b.energy.upper]) env
  unfold func171
  wp_run [func171Def]
  guard_call (interval_sub_exact env initial a.mass b.mass)
  guard_call (interval_sub_exact env initial a.momentum b.momentum)
  guard_call (interval_sub_exact env initial a.transverse b.transverse)
  guard_call (interval_sub_exact env initial a.energy b.energy)
  simp [Vectors.sub, vectorValues, boundsValues]

theorem vector_scale_exact (env : HostEnv Unit) (initial : Store Unit)
    (a : Vector) (word : UInt64) :
    TerminatesWith env Project.EulerCertificate.«module» 174 initial
      (.i64 word :: vectorValues a)
      (fun final values => final = initial ∧ values = vectorValues (Vectors.scale a word)) := by
  refine TerminatesWith.of_wp_entry_for (f := func174Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func174 _ initial
    (func174Def.toLocals [.i64 a.mass.status, .i64 a.mass.lower, .i64 a.mass.upper, .i64 a.momentum.status, .i64 a.momentum.lower, .i64 a.momentum.upper, .i64 a.transverse.status, .i64 a.transverse.lower, .i64 a.transverse.upper, .i64 a.energy.status, .i64 a.energy.lower, .i64 a.energy.upper, .i64 word]) env
  unfold func174
  wp_run [func174Def]
  guard_call (interval_scale_exact env initial a.mass word)
  guard_call (interval_scale_exact env initial a.momentum word)
  guard_call (interval_scale_exact env initial a.transverse word)
  guard_call (interval_scale_exact env initial a.energy word)
  simp [Vectors.scale, vectorValues, boundsValues]

theorem vector_divPositive_exact (env : HostEnv Unit) (initial : Store Unit)
    (a : Vector) (word : UInt64) :
    TerminatesWith env Project.EulerCertificate.«module» 66 initial
      (.i64 word :: vectorValues a)
      (fun final values => final = initial ∧ values = vectorValues (Vectors.divPositive a word)) := by
  refine TerminatesWith.of_wp_entry_for (f := func66Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func66 _ initial
    (func66Def.toLocals [.i64 a.mass.status, .i64 a.mass.lower, .i64 a.mass.upper, .i64 a.momentum.status, .i64 a.momentum.lower, .i64 a.momentum.upper, .i64 a.transverse.status, .i64 a.transverse.lower, .i64 a.transverse.upper, .i64 a.energy.status, .i64 a.energy.lower, .i64 a.energy.upper, .i64 word]) env
  unfold func66
  wp_run [func66Def]
  guard_call (interval_divPositive_exact env initial a.mass word)
  guard_call (interval_divPositive_exact env initial a.momentum word)
  guard_call (interval_divPositive_exact env initial a.transverse word)
  guard_call (interval_divPositive_exact env initial a.energy word)
  simp [Vectors.divPositive, vectorValues, boundsValues]

theorem vector_orient_exact (env : HostEnv Unit) (initial : Store Unit)
    (axis : Bool) (a : Vector) :
    TerminatesWith env Project.EulerCertificate.«module» 163 initial
      (vectorValues a ++ [.i64 (boolWord axis)])
      (fun final values => final = initial ∧ values = vectorValues (Vectors.orient axis a)) := by
  refine TerminatesWith.of_wp_entry_for (f := func163Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func163 _ initial
    (func163Def.toLocals [.i64 (boolWord axis), .i64 a.mass.status, .i64 a.mass.lower, .i64 a.mass.upper, .i64 a.momentum.status, .i64 a.momentum.lower, .i64 a.momentum.upper, .i64 a.transverse.status, .i64 a.transverse.lower, .i64 a.transverse.upper, .i64 a.energy.status, .i64 a.energy.lower, .i64 a.energy.upper]) env
  unfold func163
  wp_run [func163Def]
  cases axis <;> guard_peel
  all_goals simp [Vectors.orient, vectorValues, boundsValues]

#print axioms vector_zero_exact
#print axioms vector_state_exact
#print axioms vector_add_exact
#print axioms vector_sub_exact
#print axioms vector_scale_exact
#print axioms vector_divPositive_exact
#print axioms vector_orient_exact
end Project.EulerCertificate.Execution
