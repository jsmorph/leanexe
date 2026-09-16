import Project.TinyGpt2Hidden.Program
import Project.TinyGpt2Infer.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic

namespace Project.TinyGpt2Infer
open Project.FunctionRegion

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem componentRegion : Shift Project.TinyGpt2Hidden.module
    Project.TinyGpt2Infer.module id id (fun i => i < 71) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem component_exact {env : Wasm.HostEnv α} {initial : Wasm.Store α}
    {args : List Wasm.Value} {post : Wasm.Store α → List Wasm.Value → Prop}
    (i : Nat) (hi : i < 71)
    (h : Wasm.TerminatesWith env Project.TinyGpt2Hidden.module i initial args post) :
    Wasm.TerminatesWith env Project.TinyGpt2Infer.module i initial args post :=
  Project.FunctionRegion.terminatesWith componentRegion i hi h

#print axioms component_exact
end Project.TinyGpt2Infer
