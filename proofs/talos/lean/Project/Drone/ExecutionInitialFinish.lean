import Project.Drone.ExecutionInitialFrame

namespace Project.Drone.Execution
open Wasm Project.ProofKit WordArrayPush

set_option maxRecDepth 32768 in
theorem initial_finish_spec (env : HostEnv Unit) (store final : Store Unit)
    (seed row : UInt64) (aux : List Value) (s : Scratch) (out0 out1 : UInt64)
    (hAux : aux.length = 19) (hSeed : seed ≠ 0) (hDifferent : seed ≠ row)
    (hCall : TerminatesWith env Project.Drone.«module» 29 store [.i64 seed]
      (fun released values => released = final ∧ values = []))
    (P : Store Unit → List Value → Prop) (hNext : P final [.i64 row, .i64 row]) :
    wp Project.Drone.«module» (func23.drop 58)
      (fun c => match c with
        | .Fallthrough finish frame => P finish (frame.values.take 2)
        | .Return finish values => P finish (values.take 2)
        | _ => False)
      store (initialFrame seed row 45 true aux s out0 out1) env := by
  simp only [func23, List.drop]
  initial_calls hCall [hAux, hSeed, hDifferent, func29Def]
  exact hNext

#print axioms initial_finish_spec
end Project.Drone.Execution
