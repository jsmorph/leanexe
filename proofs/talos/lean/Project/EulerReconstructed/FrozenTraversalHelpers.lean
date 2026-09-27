import Project.EulerReconstructed.FrozenRiemannRegion
import Project.EulerRiemann.FrozenExecutionInputs
import Project.EulerRiemann.FrozenExecutionAccepted

namespace Project.EulerReconstructed.Frozen.Execution
open Wasm
open Project.Euler2DCellStep.Sweep (State orient)
open Project.EulerRiemann.Frozen.Execution (stateValues boolWord)
open Project.EulerRiemann.Frozen

theorem neighborIndex_exact (env : HostEnv Unit) (initial : Store Unit)
    (n index : Nat) (axis forward : Bool)
    (hn : 2 ≤ n ∧ n ≤ 800) (hi : index < n * n) :
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 54 initial
      [.i64 (boolWord forward), .i64 (boolWord axis),
        .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧
        values = [.i64 (UInt64.ofNat (Traversal.neighborIndex n index axis forward))]) :=
  Project.FunctionRegion.terminatesWith RiemannRegion.shift 37
    (by norm_num [RiemannRegion.domain])
    (Project.EulerRiemann.Frozen.Execution.neighborIndex_exact env initial n index axis forward hn hi)

theorem orient_exact (env : HostEnv Unit) (initial : Store Unit)
    (axis : Bool) (state : State) :
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 56 initial
      (stateValues state ++ [.i64 (boolWord axis)])
      (fun final values => final = initial ∧ values = stateValues (orient axis state)) :=
  Project.FunctionRegion.terminatesWith RiemannRegion.shift 39
    (by norm_num [RiemannRegion.domain])
    (Project.EulerRiemann.Frozen.Execution.orient_exact env initial axis state)

theorem accepted_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (grid : Array Traversal.Cell)
    (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerReconstructed.Frozen.«module» 123 initial
      [.i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (boolWord (Traversal.accepted grid))]) :=
  Project.FunctionRegion.terminatesWith RiemannRegion.shift 79
    (by norm_num [RiemannRegion.domain])
    (Project.EulerRiemann.Frozen.Execution.accepted_exact env initial owner pointer grid hGrid)

#print axioms neighborIndex_exact
#print axioms orient_exact
#print axioms accepted_exact
end Project.EulerReconstructed.Frozen.Execution
