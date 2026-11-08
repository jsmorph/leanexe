import LeanExe.Proof.Area
import LeanExe.Pipeline.Runtime

/-!
The allocator's facts at the store `initStore m cap` of `LeanExe/Proof/Area.lean`, the module's
initial store with a memory cap of `cap` pages.  `Heap.At` reads only the store's globals and
memory, and `Heap.Borrowed` only its memory, so a heap at the module's initial store and an array
borrowed there carry over to the store with the cap, which the back ends' run theorems start from.
-/

namespace LeanExe

open Wasm LeanExe.Pipeline

theorem heapAt_initStore {heap : Heap} {m : Module} (h : heap.At (m.initialStore : Store Unit))
    (cap : Nat) : heap.At (initStore m cap) :=
  ⟨h.globals, h.freeList, h.base, h.top, h.pages, h.above, h.below⟩

theorem borrowed_initStore {heap : Heap} {m : Module} {ptr : UInt64} {words : Array UInt64}
    (h : heap.Borrowed (m.initialStore : Store Unit) ptr words) (cap : Nat) :
    heap.Borrowed (initStore m cap) ptr words :=
  ⟨h.values, h.below, h.separate⟩

end LeanExe
