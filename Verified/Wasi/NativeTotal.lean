import Verified.Wasi.NativeEntry

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline

theorem native_run_total {World α : Type} {host : Host World} {signature : EffectSig}
    {native : Action α} {flatten : α → signature.result.denote} {args : Env signature.params}
    {params : List Value} {heap : Heap} {initial : Store (Observed World)}
    {runner : Nat → Result (Observed World)}
    (execution : ∃ bound, ∀ fuel ≥ bound,
      NativeFunctionResult host signature native flatten args params heap initial false (runner fuel))
    (safe : host.NoTrapsAlong native initial.host.world) :
    ∃ bound, ∀ fuel ≥ bound, ReturnOrAcceptedExit host native initial.host (runner fuel) := by
  obtain ⟨bound, execution⟩ := execution
  exact ⟨bound, fun fuel enough => (execution fuel enough).return_or_accepted_exit safe⟩

end Verified.Wasi
