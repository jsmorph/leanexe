import Project.TinyGpt2Infer.Program
import Project.F64Clip.Program
import Project.TinyGpt2Checked.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic

namespace Project.TinyGpt2Checked
open Project.FunctionRegion

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

def inferenceIndex (i : Nat) : Nat :=
  if i < 59 then i+8 else if i = 59 then 0 else if i = 60 then 67
  else if i = 61 then 4 else i+6

theorem numericalRegion : Shift Project.TinyGpt2Infer.module module
    inferenceIndex inferenceIndex (fun i => i < 78) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem numerical_exact {env : Wasm.HostEnv α} {initial : Wasm.Store α}
    {args : List Wasm.Value} {post : Wasm.Store α → List Wasm.Value → Prop}
    (i : Nat) (hi : i < 78)
    (h : Wasm.TerminatesWith env Project.TinyGpt2Infer.module i initial args post) :
    Wasm.TerminatesWith env module (inferenceIndex i) initial args post :=
  Project.FunctionRegion.terminatesWith numericalRegion i hi h

theorem clippingRegion : Shift Project.F64Clip.module module id id (fun i => i < 6) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem clipping_exact {env : Wasm.HostEnv α} {initial : Wasm.Store α}
    {args : List Wasm.Value} {post : Wasm.Store α → List Wasm.Value → Prop}
    (i : Nat) (hi : i < 6)
    (h : Wasm.TerminatesWith env Project.F64Clip.module i initial args post) :
    Wasm.TerminatesWith env module i initial args post :=
  Project.FunctionRegion.terminatesWith clippingRegion i hi h

#print axioms numerical_exact
#print axioms clipping_exact
end Project.TinyGpt2Checked
