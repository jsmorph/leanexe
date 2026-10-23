import Verified.Wasi.PureTransportSpecs
import Verified.Bytes.Allocation
import Verified.Bytes.Release
import Verified.Wasi.ABI

namespace Verified.Wasi

open Wasm LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

theorem alloc_runs {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (sourceHost : HostEnv Unit)
    (targetHost : HostEnv World) (heap : Heap) (store : Store World)
    (count : UInt64) (aborts : Bool)
    (hHeap : heap.At (PureTransport.erase store))
    (hCount : count.toNat ≤ 4294967296)
    (hCap : (PureTransport.erase store).memoryCap source 0 ≤ 65535)
    (hRoom : aborts = false → heap.Room (PureTransport.erase store) source (allocSize count)) :
    Runs aborts targetHost target 3 store [.i64 count] fun final out =>
      (heap.Fits (allocSize count) ∧
        PureTransport.erase final = heap.allocateStore (PureTransport.erase store) (allocSize count) 1 ∧
        out = [.i64 (FixedArrayAllocate.root heap.top (allocSize count) heap.free)]) ∧
      final.host = store.host := by
  have hIndex : 0 < source.funcs.length :=
    (List.getElem?_eq_some_iff.mp runtime.alloc).choose
  have hSource := alloc_spec_runs aborts runtime.memory32 runtime.imports runtime.alloc
    sourceHost heap (PureTransport.erase store) count hHeap hCount hCap hRoom
  simpa only [Nat.add_zero, PureTransport.restore_erase] using
    PureTransport.runs_transport layout profile hIndex hSource store.host

theorem release_runs {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (sourceHost : HostEnv Unit)
    (targetHost : HostEnv World) {heap : Heap} {store : Store World}
    {root length : UInt64} {bytes : LeanExe.Bytes}
    (hHeap : heap.At (PureTransport.erase store))
    (hBytes : Bytes.Rep heap (PureTransport.erase store) root length bytes) :
    TerminatesWith targetHost target 4 store [.i64 root] fun final out =>
      (out = [] ∧ PureTransport.erase final =
        Bytes.releasedStore heap (PureTransport.erase store) root) ∧
      final.host = store.host := by
  have hIndex : 1 < source.funcs.length :=
    (List.getElem?_eq_some_iff.mp runtime.release).choose
  have hSource := hBytes.release_run runtime.imports runtime.release sourceHost hHeap
  simpa only [Bytes.releasedStore, PureTransport.restore_erase] using
    PureTransport.terminatesWith_transport layout profile hIndex hSource store.host

theorem wp_alloc {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv World}
    {heap : Heap} {store : Store World} {s : Locals} {count : UInt64}
    {vs : List Value} {rest : Program} {Q : Assertion World} {aborts : Bool}
    (hHeap : heap.At (PureTransport.erase store)) (hCount : count.toNat ≤ 4294967296)
    (hCap : (PureTransport.erase store).memoryCap source 0 ≤ 65535)
    (hRoom : aborts = false → heap.Room (PureTransport.erase store) source (allocSize count))
    (hTrap : TrapOK aborts Q)
    (hNext : ∀ final : Store World, heap.Fits (allocSize count) →
      PureTransport.erase final =
        heap.allocateStore (PureTransport.erase store) (allocSize count) 1 →
      final.host = store.host →
      wp target rest Q final
        { s with values := .i64 (FixedArrayAllocate.root heap.top (allocSize count) heap.free) :: vs }
        targetHost) :
    wp target (.call 3 :: rest) Q store { s with values := .i64 count :: vs } targetHost := by
  have hRun := (alloc_runs runtime layout profile sourceHost targetHost heap store count aborts
    hHeap hCount hCap hRoom).append_args (f := Relocation.function (allocFunction 0))
      (by simp [hImports, ABI.imports])
      (by simpa [hImports, ABI.imports] using layout.functions runtime.alloc)
      (by rfl) vs
  refine wp_call_runs hRun hTrap ?_
  intro final out hPost
  obtain ⟨values, rfl, ⟨hFits, hStore, rfl⟩, hWorld⟩ := hPost
  exact hNext final hFits hStore hWorld

theorem wp_release {World : Type} {source target : Module}
    (runtime : Runtime source) (layout : Relocation.Layout source target)
    (profile : Relocation.Profile source) (hImports : target.imports = ABI.imports)
    (sourceHost : HostEnv Unit) {targetHost : HostEnv World}
    {heap : Heap} {store : Store World} {s : Locals}
    {root length : UInt64} {bytes : LeanExe.Bytes} {vs : List Value}
    {rest : Program} {Q : Assertion World}
    (hHeap : heap.At (PureTransport.erase store))
    (hBytes : Bytes.Rep heap (PureTransport.erase store) root length bytes)
    (hNext : ∀ final : Store World,
      PureTransport.erase final = Bytes.releasedStore heap (PureTransport.erase store) root →
      final.host = store.host → wp target rest Q final { s with values := vs } targetHost) :
    wp target (.call 4 :: rest) Q store { s with values := .i64 root :: vs } targetHost := by
  have hRun := ((release_runs runtime layout profile sourceHost targetHost hHeap hBytes).runs
    (aborts := false)).append_args (f := Relocation.function (releaseFunction 1))
      (by simp [hImports, ABI.imports])
      (by simpa [hImports, ABI.imports] using layout.functions runtime.release)
      (by rfl) vs
  refine wp_call_runs hRun trivial ?_
  intro final out hPost
  obtain ⟨values, rfl, ⟨rfl, hStore⟩, hWorld⟩ := hPost
  exact hNext final hStore hWorld

end Verified.Wasi
