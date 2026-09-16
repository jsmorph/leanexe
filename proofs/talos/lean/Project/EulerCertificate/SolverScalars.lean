import Project.EulerCertificate.SolverRegion
import Project.EulerReconstructed.Scalars
import Project.EulerReconstructed.TraversalHelpers
import Project.EulerReconstructed.TimeTransfers

namespace Project.EulerCertificate.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State orient)
open Project.EulerRiemann
open Project.EulerRiemann.Execution (stateValues boolWord)
open Project.EulerReconstruction.Execution (facesValues)
open Project.EulerOutwardSpeed.Execution (checkedValues)

theorem smallNaturalBits_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (hn : n ≤ 800) :
    TerminatesWith env Project.EulerCertificate.«module» 54 initial [.i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = [.i64 (Time.smallNaturalBits n)]) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 47 (by norm_num [SolverRegion.domain])
    (Project.FunctionRegion.terminatesWith Project.EulerReconstructed.RiemannRegion.shift 33
      (by norm_num [Project.EulerReconstructed.RiemannRegion.domain])
      (Project.EulerRiemann.Execution.smallNaturalBits_exact env initial n hn))

theorem state_orient_exact (env : HostEnv Unit) (initial : Store Unit)
    (axis : Bool) (q : State) :
    TerminatesWith env Project.EulerCertificate.«module» 97 initial
      (stateValues q ++ [.i64 (boolWord axis)])
      (fun final values => final = initial ∧ values = stateValues (orient axis q)) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 56 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.orient_exact env initial axis q)

theorem reconstruct_exact (env : HostEnv Unit) (initial : Store Unit) (fuel : UInt64)
    (left center right : State) :
    TerminatesWith env Project.EulerCertificate.«module» 116 initial
      (stateValues right ++ stateValues center ++ stateValues left ++ [.i64 fuel])
      (fun final values => final = initial ∧ values =
        facesValues (Reconstruction.reconstruct fuel.toNat left center right)) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 75 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.reconstruct_exact env initial fuel left center right)

theorem selected_flux_exact (env : HostEnv Unit) (initial : Store Unit) (left right : State) :
    TerminatesWith env Project.EulerCertificate.«module» 132 initial
      (stateValues right ++ stateValues left)
      (fun final values => final = initial ∧ values =
        Project.EulerOutwardFlux.Execution.fluxValues
          left.density left.mx left.my left.energy right.density right.mx right.my right.energy) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 93 (by norm_num [SolverRegion.domain])
    (Project.FunctionRegion.terminatesWith Project.EulerReconstructed.FaceRegion.shift 54
      (by norm_num [Project.EulerReconstructed.FaceRegion.domain])
      (Project.EulerOutwardFaceStep.Execution.flux_exact env initial
        left.density left.mx left.my left.energy right.density right.mx right.my right.energy))

theorem accepted_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerCertificate.«module» 161 initial
      [.i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Traversal.accepted grid))]) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 123 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.accepted_exact env initial owner pointer grid hGrid)

theorem gridRatioChecked_exact (env : HostEnv Unit) (initial : Store Unit)
    (n dt alpha : UInt64) :
    TerminatesWith env Project.EulerCertificate.«module» 95 initial
      [.i64 alpha, .i64 dt, .i64 n]
      (fun final values => final = initial ∧ values =
        checkedValues (OutwardCfl.gridRatioChecked n.toNat dt alpha)) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 53 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.gridRatioChecked_exact env initial n dt alpha)

theorem endTime_exact (env : HostEnv Unit) (initial : Store Unit) :
    TerminatesWith env Project.EulerCertificate.«module» 76 initial []
      (fun final values => final = initial ∧ values = [.i64 Time.endTime]) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 0 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.endTime_exact env initial)

theorem validAdvance_exact (env : HostEnv Unit) (initial : Store Unit) (time dt : UInt64) :
    TerminatesWith env Project.EulerCertificate.«module» 92 initial [.i64 dt, .i64 time]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Time.validAdvance time dt))]) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 50 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.validAdvance_exact env initial time dt)

theorem proposal_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (time alpha : UInt64) (hn : n ≤ 800) :
    TerminatesWith env Project.EulerCertificate.«module» 91 initial
      [.i64 alpha, .i64 time, .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = [.i64 (Time.proposal n time alpha)]) :=
  Project.FunctionRegion.terminatesWith SolverRegion.shift 49 (by norm_num [SolverRegion.domain])
    (Project.EulerReconstructed.Execution.proposal_exact env initial n time alpha hn)

#print axioms smallNaturalBits_exact
#print axioms state_orient_exact
#print axioms reconstruct_exact
#print axioms selected_flux_exact
#print axioms accepted_exact
#print axioms gridRatioChecked_exact
#print axioms endTime_exact
#print axioms validAdvance_exact
#print axioms proposal_exact
end Project.EulerCertificate.Execution
