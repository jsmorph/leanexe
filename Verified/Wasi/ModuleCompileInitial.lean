import Verified.Wasi.ModuleInitial
import Verified.Instantiate

namespace Verified.Wasi.Module

open Wasm LeanExe.Pipeline

theorem initialStore_at (source : Wasm.Module) (extra : Extension) (world : World)
    {heap : Heap} (h : heap.At (source.initialStore : Store Unit)) :
    heap.At (PureTransport.erase (initialStore source extra world)) :=
  ⟨h.globals, h.freeList, h.base, h.top, h.pages, h.above, h.below⟩

theorem initialStore_borrowed (source : Wasm.Module) (extra : Extension) (world : World)
    {heap : Heap} {pointer : UInt64} {words : Array UInt64}
    (h : heap.Borrowed (source.initialStore : Store Unit) pointer words) :
    heap.Borrowed (PureTransport.erase (initialStore source extra world)) pointer words :=
  ⟨h.values, h.below, h.separate⟩

theorem initialStore_static (source : Wasm.Module) (extra : Extension) (world : World)
    {pool : Bytes.LiteralPool} {heap : Heap}
    (h : pool.Static heap (source.initialStore : Store Unit)) :
    pool.Static heap (PureTransport.erase (initialStore source extra world)) := h

theorem initialStore_scratch (source : Wasm.Module) (extra : Extension) (world : World)
    {heap : Heap} (h : heap.At (source.initialStore : Store Unit)) :
    16 ≤ (initialStore source extra world).mem.pages * 65536 := by
  change 16 ≤ (source.initialStore : Store Unit).mem.pages * 65536
  have hBase := h.base
  have hTop := h.top
  omega

theorem compileWith_initialStaticStore {S : List Sig} (prog : Prog S)
    (tables : List (Array UInt64)) (wrappers : List (Wrapper S tables.length))
    (pool : Bytes.LiteralPool) (extra : Extension) (world : World)
    (hPoolBase : pool.base = tablesEnd tables) (hFit : pool.top ≤ 65535 * 65536) :
    let source := Verified.compileWith prog tables wrappers pool
    let store := PureTransport.erase (initialStore source extra world)
    (initialStaticHeap pool).At store ∧
      store.memoryCap (assemble source extra) 0 ≤ 65535 ∧
      (∀ k (hk : k < tables.length),
        (initialStaticHeap pool).Borrowed store (tableAddr tables k) tables[k]) ∧
      pool.Static (initialStaticHeap pool) store := by
  obtain ⟨hAt, hCap, hBorrowed, hStatic⟩ :=
    Verified.compileWith_initialStaticStore prog tables wrappers pool hPoolBase hFit
  exact ⟨initialStore_at _ extra world hAt, hCap,
    (fun k hk => initialStore_borrowed _ extra world (hBorrowed k hk)),
    initialStore_static _ extra world hStatic⟩

end Verified.Wasi.Module
