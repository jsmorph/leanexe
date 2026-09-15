import Project.EulerOutwardFaceStep.Program
import Project.EulerOutwardFlux.Execution

namespace Project.EulerOutwardFaceStep.Execution
open Wasm Project.FunctionRegion
open Project.EulerConservative.Execution (boolWord)
open Project.EulerOutwardSpeed.Execution (checkedValues)

def fluxDomain (index : Nat) : Prop := index ≤ 54

set_option maxRecDepth 32768 in
theorem fluxShift :
    Shift Project.EulerOutwardFlux.«module» Project.EulerOutwardFaceStep.«module»
      id id fluxDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  have hi : index ≤ 54 := hi
  interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [fluxDomain]

theorem positive_exact (env : HostEnv Unit) (initial : Store Unit) (word : UInt64) :
    TerminatesWith env Project.EulerOutwardFaceStep.«module» 0 initial [.i64 word]
      (fun final values => final = initial ∧
        values = [.i64 (boolWord (Project.Euler2DConservative.Model.positiveBits word))]) :=
  Project.FunctionRegion.terminatesWith fluxShift 0 (by norm_num [fluxDomain])
    (Project.EulerOutwardFlux.Execution.side_positive_exact env initial word)

theorem mul_exact (env : HostEnv Unit) (initial : Store Unit) (up : Bool) (a b : UInt64) :
    TerminatesWith env Project.EulerOutwardFaceStep.«module» 25 initial
      [.i64 b, .i64 a, .i64 (boolWord up)]
      (fun final values => final = initial ∧
        values = checkedValues (Project.ProofKit.F64Outward.mul up a b)) :=
  Project.FunctionRegion.terminatesWith fluxShift 25 (by norm_num [fluxDomain])
    (Project.FunctionRegion.terminatesWith Project.EulerOutwardFlux.Execution.speedShift 25
      (by norm_num [Project.EulerOutwardFlux.Execution.speedDomain])
      (Project.EulerOutwardSpeed.Execution.mul_exact env initial up a b))

theorem side_exact (env : HostEnv Unit) (initial : Store Unit) (rho mx my energy : UInt64) :
    TerminatesWith env Project.EulerOutwardFaceStep.«module» 38 initial
      [.i64 energy, .i64 my, .i64 mx, .i64 rho]
      (fun final values => final = initial ∧
        values = Project.EulerOutwardFlux.Execution.sideValues rho mx my energy) :=
  Project.FunctionRegion.terminatesWith fluxShift 38 (by norm_num [fluxDomain])
    (Project.EulerOutwardFlux.Execution.side_exact env initial rho mx my energy)

theorem flux_exact (env : HostEnv Unit) (initial : Store Unit)
    (rhoL mxL myL energyL rhoR mxR myR energyR : UInt64) :
    TerminatesWith env Project.EulerOutwardFaceStep.«module» 54 initial
      [.i64 energyR, .i64 myR, .i64 mxR, .i64 rhoR, .i64 energyL, .i64 myL, .i64 mxL, .i64 rhoL]
      (fun final values => final = initial ∧
        values = Project.EulerOutwardFlux.Execution.fluxValues rhoL mxL myL energyL rhoR mxR myR energyR) :=
  Project.FunctionRegion.terminatesWith fluxShift 54 (by norm_num [fluxDomain])
    (Project.EulerOutwardFlux.Execution.flux_exact env initial rhoL mxL myL energyL rhoR mxR myR energyR)

def updateDomain (index : Nat) : Prop :=
  (41 ≤ index ∧ index ≤ 44) ∨ index = 57 ∨ index = 58

def updateRename (index : Nat) : Nat := if 57 ≤ index then index + 4 else index

theorem updateShift :
    Shift Project.EulerRiemann.«module» Project.EulerOutwardFaceStep.«module»
      updateRename updateRename updateDomain := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro index hi
  rcases hi with ⟨hlo, hhi⟩ | rfl | rfl
  all_goals try interval_cases index
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [updateDomain]

theorem update_exact (env : HostEnv Unit) (initial : Store Unit)
    (ratio state fluxL fluxR : UInt64) :
    TerminatesWith env Project.EulerOutwardFaceStep.«module» 62 initial
      [.i64 fluxR, .i64 fluxL, .i64 state, .i64 ratio]
      (fun final values => final = initial ∧
        values = Project.EulerCellStep.Execution.updateValues ratio state fluxL fluxR) :=
  Project.FunctionRegion.terminatesWith updateShift 58 (by norm_num [updateDomain])
    (Project.EulerRiemann.Execution.update_exact env initial ratio state fluxL fluxR)

theorem rejectedCell_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerOutwardFaceStep.«module» 68 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) := by
  refine TerminatesWith.of_wp_entry_for (f := func68Def) rfl ?_ (by decide)
  change wp Project.EulerOutwardFaceStep.«module» func68 _ initial (func68Def.toLocals []) env
  unfold func68
  wp_run
  simp [func68Def, List.set]

#print axioms fluxShift
#print axioms positive_exact
#print axioms mul_exact
#print axioms side_exact
#print axioms flux_exact
#print axioms updateShift
#print axioms update_exact
#print axioms rejectedCell_exact
end Project.EulerOutwardFaceStep.Execution
