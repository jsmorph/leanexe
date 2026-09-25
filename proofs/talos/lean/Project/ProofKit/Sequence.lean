import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Semantics.Lemmas

namespace Project.ProofKit.Sequence
open Wasm

def Fallthrough (P : Store α → Locals → Prop) : Continuation α → Prop
  | .Fallthrough st frame => P st frame
  | _ => False

theorem exec_append {α : Type} {fuel : Nat} {m : Wasm.Module}
    {st : Store α} {frame : Locals} {env : HostEnv α} (left right : Program) :
    exec fuel m st frame (left ++ right) env =
      match exec fuel m st frame left env with
      | .Fallthrough nextStore nextFrame => exec fuel m nextStore nextFrame right env
      | result => result := by
  induction left generalizing st frame with
  | nil => simp only [List.nil_append, exec]
  | cons inst rest ih =>
      simp only [List.cons_append, exec]
      cases execOne fuel m st frame inst env <;> simp only
      exact ih

theorem wp_append (hLeft : wp m left (Fallthrough P) st frame env)
    (hRight : ∀ nextStore nextFrame, P nextStore nextFrame →
      wp m right Q nextStore nextFrame env) :
    wp m (left ++ right) Q st frame env := by
  unfold wp at hLeft ⊢
  obtain ⟨leftFuel, hLeft⟩ := hLeft
  have hAt := hLeft leftFuel (Nat.le_refl _)
  cases hResult : exec leftFuel m st frame left env <;>
    simp only [hResult, Fallthrough] at hAt
  case Fallthrough nextStore nextFrame =>
    have hNext := hRight nextStore nextFrame hAt
    unfold wp at hNext
    obtain ⟨rightFuel, hRight⟩ := hNext
    refine ⟨max leftFuel rightFuel, fun fuel hFuel => ?_⟩
    have hLeftLe : leftFuel ≤ fuel := (Nat.le_max_left _ _).trans hFuel
    have hRightLe : rightFuel ≤ fuel := (Nat.le_max_right _ _).trans hFuel
    have hSame : exec fuel m st frame left env = exec leftFuel m st frame left env :=
      exec_fuel_mono hLeftLe (by simp [hResult])
    rw [exec_append, hSame, hResult]
    exact hRight fuel hRightLe

#print axioms wp_append
end Project.ProofKit.Sequence
