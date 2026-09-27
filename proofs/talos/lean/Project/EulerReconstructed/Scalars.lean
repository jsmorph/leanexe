import Project.EulerReconstructed.FaceRegion
import Project.EulerReconstructed.ReconstructionRegion
import Project.EulerReconstructed.GridRegion
import Project.EulerReconstructed.CflRegion
import Project.EulerOutwardFaceStep.Execution
import Project.EulerReconstruction.Reconstruct
import Project.EulerOutwardGrid.Cell
import Project.EulerOutwardCfl.Spec

namespace Project.EulerReconstructed.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State)
open Project.EulerReconstruction.Execution (stateValues facesValues)
open Project.EulerOutwardFaceStep.Execution (arguments cellValues)
open Project.EulerOutwardSpeed.Execution (checkedValues)
open Project.EulerRiemann.OutwardNumerics

theorem reconstruct_exact (env : HostEnv Unit) (initial : Store Unit) (fuel : UInt64)
    (left center right : State) :
    TerminatesWith env Project.EulerReconstructed.«module» 75 initial
      (stateValues right ++ stateValues center ++ stateValues left ++ [.i64 fuel])
      (fun final values => final = initial ∧ values =
        facesValues (Project.EulerRiemann.Reconstruction.reconstruct fuel.toNat left center right)) :=
  Project.FunctionRegion.terminatesWith ReconstructionRegion.shift 40
    (by norm_num [ReconstructionRegion.domain])
    (Project.EulerReconstruction.Execution.reconstruct_exact env initial fuel left center right)

theorem face_step_exact (env : HostEnv Unit) (initial : Store Unit) (ratio : UInt64)
    (center leftOuter leftInner rightInner rightOuter : State) :
    TerminatesWith env Project.EulerReconstructed.«module» 105 initial
      (arguments ratio center leftOuter leftInner rightInner rightOuter)
      (fun final values => final = initial ∧ values =
        cellValues (faceStepCheckedBits ratio center leftOuter leftInner rightInner rightOuter)) :=
  Project.FunctionRegion.terminatesWith FaceRegion.shift 70
    (by norm_num [FaceRegion.domain])
    (Project.EulerOutwardFaceStep.Execution.face_step_exact env initial ratio
      center leftOuter leftInner rightInner rightOuter)

theorem rejectedCell_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerReconstructed.«module» 103 initial []
      (fun final values => final = initial ∧
        values = [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 1]) :=
  Project.FunctionRegion.terminatesWith FaceRegion.shift 68
    (by norm_num [FaceRegion.domain])
    (Project.EulerOutwardFaceStep.Execution.rejectedCell_exact env initial)

theorem scanCell_exact (env : HostEnv Unit) (initial : Store Unit)
    (acc : Project.ProofKit.F64Outward.Checked) (cell : Project.EulerRiemann.Traversal.Cell) :
    TerminatesWith env Project.EulerReconstructed.«module» 45 initial
      [.i64 cell.status, .i64 cell.pressure, .i64 cell.state.energy,
        .i64 cell.state.my, .i64 cell.state.mx, .i64 cell.state.density,
        .i64 (UInt64.ofNat cell.index), .i64 acc.value, .i64 acc.status]
      (fun final values => final = initial ∧ values =
        checkedValues (Project.EulerRiemann.OutwardMaximum.scanCell acc cell)) :=
  Project.FunctionRegion.terminatesWith GridRegion.shift 44
    (by norm_num [GridRegion.domain])
    (Project.EulerOutwardGrid.Execution.scanCell_exact env initial acc cell)

theorem gridRatioChecked_exact (env : HostEnv Unit) (initial : Store Unit)
    (n dt alpha : UInt64) :
    TerminatesWith env Project.EulerReconstructed.«module» 53 initial
      [.i64 alpha, .i64 dt, .i64 n]
      (fun final values => final = initial ∧ values = checkedValues
        (Project.EulerRiemann.OutwardCfl.gridRatioChecked n.toNat dt alpha)) :=
  Project.FunctionRegion.terminatesWith CflRegion.shift 15
    (by norm_num [CflRegion.domain])
    (Project.EulerOutwardCfl.Spec.gridRatioChecked_exact env initial n dt alpha)

#print axioms reconstruct_exact
#print axioms face_step_exact
#print axioms rejectedCell_exact
#print axioms scanCell_exact
#print axioms gridRatioChecked_exact
end Project.EulerReconstructed.Execution
