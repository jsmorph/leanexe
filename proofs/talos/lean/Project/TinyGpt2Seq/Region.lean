import Project.TinyGpt2Seq.Program
import Project.TinyGpt2Hidden.Program
import Project.TinyGpt2Checked.Program
import Project.SequenceSoftmax.Program
import Project.FunctionRegion.Exec
import Mathlib.Tactic

namespace Project.TinyGpt2Seq
open Project.FunctionRegion

set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

def sharedIndex : Nat → Nat
  | 0 => 15
  | 1 => 16
  | 2 => 17
  | 3 => 18
  | 4 => 25
  | 5 => 10
  | 6 => 26
  | 7 => 27
  | 8 => 28
  | 9 => 11
  | 10 => 12
  | 11 => 13
  | 12 => 14
  | 13 => 19
  | 14 => 20
  | 15 => 21
  | 16 => 22
  | 17 => 23
  | 23 => 30
  | 24 => 31
  | 25 => 32
  | 26 => 33
  | 32 => 45
  | 35 => 38
  | 36 => 39
  | 37 => 40
  | 38 => 41
  | 39 => 42
  | 40 => 43
  | 45 => 50
  | 59 => 2
  | 60 => 60
  | 61 => 6
  | 62 => 61
  | 63 => 62
  | 64 => 63
  | 65 => 64
  | 66 => 65
  | 67 => 66
  | 68 => 67
  | 69 => 68
  | _ => 0

def SharedFunction (i : Nat) : Prop :=
  i ≤ 17 ∨ (23 ≤ i ∧ i ≤ 26) ∨ i = 32 ∨ (35 ≤ i ∧ i ≤ 40) ∨ i = 45 ∨ (59 ≤ i ∧ i ≤ 69)

theorem sharedRegion : Shift Project.TinyGpt2Hidden.module module
    sharedIndex sharedIndex SharedFunction := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  have hUpper : i ≤ 69 := by unfold SharedFunction at hi; omega
  interval_cases i
  all_goals try (simp only [SharedFunction] at hi; omega)
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num [SharedFunction]

theorem shared_exact {env : Wasm.HostEnv α} {initial : Wasm.Store α}
    {args : List Wasm.Value} {post : Wasm.Store α → List Wasm.Value → Prop}
    (i : Nat) (hi : SharedFunction i)
    (h : Wasm.TerminatesWith env Project.TinyGpt2Hidden.module i initial args post) :
    Wasm.TerminatesWith env module (sharedIndex i) initial args post :=
  Project.FunctionRegion.terminatesWith sharedRegion i hi h

theorem sequenceRegion : Shift Project.SequenceSoftmax.module module
    (fun i => i+38) (fun i => i+38) (fun i => i ≤ 10) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem sequence_exact {env : Wasm.HostEnv α} {initial : Wasm.Store α}
    {args : List Wasm.Value} {post : Wasm.Store α → List Wasm.Value → Prop}
    (i : Nat) (hi : i ≤ 10)
    (h : Wasm.TerminatesWith env Project.SequenceSoftmax.module i initial args post) :
    Wasm.TerminatesWith env module (i+38) initial args post :=
  Project.FunctionRegion.terminatesWith sequenceRegion i hi h

theorem clippingRegion : Shift Project.TinyGpt2Checked.module module
    (fun i => i+2) (fun i => i+2) (fun i => i ≤ 6) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro i hi
  interval_cases i
  all_goals refine ⟨_, rfl, rfl, ?_⟩
  all_goals prove_portable
  all_goals norm_num

theorem clipping_exact {env : Wasm.HostEnv α} {initial : Wasm.Store α}
    {args : List Wasm.Value} {post : Wasm.Store α → List Wasm.Value → Prop}
    (i : Nat) (hi : i ≤ 6)
    (h : Wasm.TerminatesWith env Project.TinyGpt2Checked.module i initial args post) :
    Wasm.TerminatesWith env module (i+2) initial args post :=
  Project.FunctionRegion.terminatesWith clippingRegion i hi h

theorem releaseRegion : Shift Project.SequenceSoftmax.module module
    (fun _ => 82) (fun _ => 82) (fun i => i = 15) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  rintro i rfl
  refine ⟨_, rfl, rfl, ?_⟩
  prove_portable
  all_goals rfl

#print axioms shared_exact
#print axioms sequence_exact
#print axioms clipping_exact
#print axioms releaseRegion
end Project.TinyGpt2Seq
