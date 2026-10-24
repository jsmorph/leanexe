import Verified.Examples.WasiRetainBudget

namespace Verified.Examples.WasiRetain

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime Verified Verified.Wasi

theorem initial_within {World : Type} (world : Observed World) :
    (initialStaticHeap compiled.literalPool).Within
      (PureTransport.erase (compileInitialStore compiled.pure.module compiled.program
        compiled.entries none compiled.literalPool world)) compiled.pure.module 112 := by
  change 4096 + 112 ≤ 65536 * 65535
  decide

theorem retain_total {World : Type} (host : Host World) (world : Observed World)
    (targetHost : HostEnv (Observed World))
    (valid : targetHost.Satisfies compiled.module (hostSpec host))
    (safe : host.NoTrapsAlong retain world.world) :
    let initial := compileInitialStore compiled.pure.module compiled.program
      compiled.entries none compiled.literalPool world
    ∃ bound, ∀ fuel ≥ bound, ReturnOrAcceptedExit host retain world
      (run fuel compiled.module (Wrappers.effectIndex compiled.pure.module 1)
        initial [] targetHost) := by
  let initial := compileInitialStore compiled.pure.module compiled.program
    compiled.entries none compiled.literalPool world
  have initialized := compiled.initial world
  apply compiled.retain.total (host := host) (targetHost := targetHost)
    (initial := initial) (heap := initialStaticHeap compiled.literalPool)
    (visibleWords := []) (budget := 112)
  · rfl
  · exact valid
  · exact initialized.1
  · rfl
  · exact Separate.nil
  · exact ⟨initialized.2.2.2, fun _ _ => Apart.nil⟩
  · intro region membership
    exact nomatch membership
  · exact initialized.2.1
  · intro _
    exact ⟨initial_within world, call_prefix_bound (observedHost host) world⟩
  · exact safe

end Verified.Examples.WasiRetain
