import Interpreter.Wasm.Wp.Defs
import Interpreter.Wasm.Semantics.Lemmas

namespace Wasm

theorem exec_append_match (fuel : Nat) (m : Module) (host : HostEnv World)
    (store : Store World) (locals : Locals) (first next : Program) :
    exec fuel m store locals (first ++ next) host =
      match exec fuel m store locals first host with
      | .Fallthrough state after => exec fuel m state after next host
      | other => other := by
  induction first generalizing store locals with
  | nil => simp only [List.nil_append, exec]
  | cons instruction rest ih =>
    simp only [List.cons_append, exec]
    cases execOne fuel m store locals instruction host with
    | Fallthrough state after => exact ih state after
    | _ => rfl

def Then (host : HostEnv World) (m : Module) (rest : Program)
    (Q : Assertion World) : Assertion World
  | .Fallthrough store locals => wp m rest Q store locals host
  | .OutOfFuel => False
  | other => Q other

theorem wp_append {host : HostEnv World} {m : Module} {first rest : Program}
    {Q : Assertion World} {store : Store World} {locals : Locals}
    (h : wp m first (Then host m rest Q) store locals host) :
    wp m (first ++ rest) Q store locals host := by
  unfold wp at h ⊢
  obtain ⟨bound, hBound⟩ := h
  have hAt := hBound bound le_rfl
  have hNotFuel : exec bound m store locals first host ≠ .OutOfFuel := by
    intro hFuel
    simpa only [hFuel, Then] using hAt
  cases hResult : exec bound m store locals first host with
  | Fallthrough after finalLocals =>
    simp only [hResult, Then] at hAt
    unfold wp at hAt
    obtain ⟨tailBound, hTail⟩ := hAt
    refine ⟨max bound tailBound, fun fuel hFuel => ?_⟩
    rw [exec_append_match, exec_fuel_mono (by omega : bound ≤ fuel) hNotFuel, hResult]
    exact hTail fuel (by omega)
  | OutOfFuel => exact False.elim (hNotFuel hResult)
  | _ =>
    simp only [hResult, Then] at hAt
    refine ⟨bound, fun fuel hFuel => ?_⟩
    rw [exec_append_match, exec_fuel_mono hFuel hNotFuel, hResult]
    exact hAt

end Wasm
