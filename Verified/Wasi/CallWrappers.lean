import Verified.Wasi.ReadFunction
import Verified.Wasi.Wrappers

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_call_returned_at {World : Type} {m : Module} {env : HostEnv World}
    {initial final : Store World} {s : Locals} {index fuel : Nat} {values : List Value}
    {rest : Program} {Q : Assertion World}
    (hRun : run fuel m index initial s.values env = .Success values final)
    (hNext : wp m rest Q final { s with values } env) :
    wp m (.call index :: rest) Q initial s env := by
  refine wp_call_at (Post := fun current out => current = final ∧ out = values) ?_ ?_
  · refine ⟨fuel, fun next hFuel => ⟨values, final, ?_, rfl, rfl⟩⟩
    rw [run_fuel_mono hFuel (by rw [hRun]; intro h; cases h)]
    exact hRun
  · rintro current out ⟨rfl, rfl⟩
    exact hNext

theorem wp_call_trapped_at {World : Type} {m : Module} {env : HostEnv World}
    {initial final : Store World} {s : Locals} {index fuel : Nat} {message : String}
    {rest : Program} {Q : Assertion World}
    (hRun : run fuel m index initial s.values env = .Trap final message)
    (hTrap : Q (.Trap final message)) :
    wp m (.call index :: rest) Q initial s env := by
  unfold wp
  refine ⟨fuel + 1, fun next hFuel => ?_⟩
  obtain ⟨next, rfl⟩ : ∃ previous, next = previous + 1 := ⟨next - 1, by omega⟩
  rw [exec_call_cons,
    run_fuel_mono (by omega : fuel ≤ next) (by rw [hRun]; intro h; cases h), hRun]
  exact hTrap

end Verified.Wasi
