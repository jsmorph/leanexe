import Verified.Wasi.Runtime

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem wp_call_runs_frame {World : Type} {m : Module} {env : HostEnv World}
    {store : Store World} {s : Locals} {index : Nat} {aborts : Bool}
    {rest : Program} {Q : Assertion World} {Post : Store World → List Value → Prop}
    (hRun : Runs aborts env m index store s.values Post)
    (hWorld : ∀ fuel final, run fuel m index store s.values env = .Trap final "unreachable" →
      final.host = store.host)
    (hTrap : aborts = true → ∀ final : Store World,
      final.host = store.host → Q (.Trap final "unreachable"))
    (hPost : ∀ final values, Post final values →
      wp m rest Q final { s with values } env) :
    wp m (.call index :: rest) Q store s env := by
  obtain ⟨bound, hBound⟩ := hRun
  rcases hBound bound le_rfl with ⟨values, final, hRun, hPostValues⟩ | hTrapped
  · refine wp_call_at ⟨bound, fun fuel hFuel => ?_⟩ hPost
    rw [run_fuel_mono hFuel (by rw [hRun]; intro h; cases h)]
    exact ⟨values, final, hRun, hPostValues⟩
  · cases aborts with
    | false => exact hTrapped.elim
    | true =>
      obtain ⟨final, hRun⟩ := hTrapped
      unfold wp
      refine ⟨bound + 1, fun fuel hFuel => ?_⟩
      obtain ⟨fuel, rfl⟩ : ∃ fuel', fuel = fuel' + 1 := ⟨fuel - 1, by omega⟩
      rw [exec_call_cons,
        run_fuel_mono (by omega : bound ≤ fuel) (by rw [hRun]; intro h; cases h), hRun]
      exact hTrap rfl final (hWorld bound final hRun)

theorem wp_alloc_frame {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv World}
    {heap : Heap} {store : Store World} {s : Locals} {count : UInt64}
    {values : List Value} {rest : Program} {Q : Assertion World} {aborts : Bool}
    (hHeap : heap.At (PureTransport.erase store)) (hCount : count.toNat ≤ 4294967296)
    (hCap : (PureTransport.erase store).memoryCap source 0 ≤ 65535)
    (hRoom : aborts = false → heap.Room (PureTransport.erase store) source (allocSize count))
    (hTrap : aborts = true → ∀ final : Store World,
      final.host = store.host → Q (.Trap final "unreachable"))
    (hNext : ∀ final : Store World, heap.Fits (allocSize count) →
      PureTransport.erase final =
        heap.allocateStore (PureTransport.erase store) (allocSize count) 1 →
      final.host = store.host →
      wp target rest Q final
        { s with values := .i64 (FixedArrayAllocate.root heap.top (allocSize count) heap.free) ::
          values } targetHost) :
    wp target (.call 3 :: rest) Q store { s with values := .i64 count :: values } targetHost := by
  have hRuns := (alloc_runs runtime layout profile sourceHost targetHost heap store count aborts
    hHeap hCount hCap hRoom).append_args (f := Relocation.function (allocFunction 0))
      (by simp [hImports, ABI.imports])
      (by simpa [hImports, ABI.imports] using layout.functions runtime.alloc)
      (by rfl) values
  refine wp_call_runs_frame hRuns ?_ hTrap ?_
  · intro fuel final hRun
    have hIndex : 0 < source.funcs.length :=
      (List.getElem?_eq_some_iff.mp runtime.alloc).choose
    have hWorld := PureTransport.entry_keepsWorld layout profile hIndex fuel
      (PureTransport.erase store) store.host (.i64 count :: values) sourceHost targetHost
    simpa only [PureTransport.restore_erase, Nat.add_zero, hRun, PureTransport.KeepsWorld] using hWorld
  · intro final out hPost
    obtain ⟨calleeValues, rfl, ⟨hFits, hStore, rfl⟩, hWorld⟩ := hPost
    exact hNext final hFits hStore hWorld

end Verified.Wasi
