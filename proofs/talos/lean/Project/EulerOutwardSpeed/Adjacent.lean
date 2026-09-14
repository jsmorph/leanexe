import Project.EulerOutwardSpeed.Guard
import Project.ProofKit.F64Outward

namespace Project.EulerOutwardSpeed.Execution
open Wasm
open Project.EulerConservative.Execution (boolWord)
open Project.ProofKit.F64Adjacent (nextUp nextDown)

theorem nextUp_exact (env : HostEnv Unit) (initial : Store Unit) (bits : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 19 initial [.i64 bits]
      (fun final values => final = initial ∧ values = [.i64 (nextUp bits)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func19Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func19 _ initial
    (func19Def.toLocals [.i64 bits]) env
  unfold func19
  by_cases hz : bits = 0x8000000000000000
  all_goals by_cases hp : bits < 0x8000000000000000
  all_goals wp_run [func19Def, hz, hp]
  all_goals guard_peel
  all_goals simp [nextUp, hz, hp]

theorem nextDown_exact (env : HostEnv Unit) (initial : Store Unit) (bits : UInt64) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 20 initial [.i64 bits]
      (fun final values => final = initial ∧ values = [.i64 (nextDown bits)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func20Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func20 _ initial
    (func20Def.toLocals [.i64 bits]) env
  unfold func20
  by_cases hz : bits = 0
  all_goals by_cases hp : bits < 0x8000000000000000
  all_goals wp_run [func20Def, hz, hp]
  all_goals guard_peel
  all_goals simp [nextDown, hz, hp]

theorem rejected_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerOutwardSpeed.«module» 22 initial []
      (fun final values => final = initial ∧ values = [.i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func22Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardSpeed.«module» func22 _ initial
    (func22Def.toLocals []) env
  unfold func22
  wp_run [func22Def]
  simp

#print axioms nextUp_exact
#print axioms nextDown_exact
#print axioms rejected_exact
end Project.EulerOutwardSpeed.Execution
