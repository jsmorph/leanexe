import Verified.TreeFieldsMemory
import Verified.HeapStep

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

theorem RecordStorage.writeValues {width : Nat} {heap : Heap} {store : Store Unit}
    {ptr : UInt64} (h : RecordStorage width heap store ptr) (hAt : heap.At store)
    (i : Nat) (words : List UInt64) (hLength : i + words.length ≤ width) :
    let store' := recordWriteValues ptr i words store
    heap.At store' ∧ RecordStorage width heap store' ptr ∧
      capacityAt store' ptr = capacityAt store ptr ∧
      Step heap store (fun r => regionsDisjoint r (block store ptr)) heap store' [] := by
  have hCapacity := h.capacity
  have hBase := h.base
  have hAddress := h.address
  have hWrites := recordWriteValues_range ptr i words store (by omega)
  obtain ⟨hAt', hRaw', hCap'⟩ := h.write hAt hWrites (by omega) (by omega) (by omega)
    (Or.inr (by omega))
  exact ⟨hAt', hRaw', hCap', Step.ofWritesRange hAt' hWrites
    (by simp only [block]; omega) (by simp only [block]; omega)⟩

theorem RecordStorage.writeValues_header {width : Nat} {heap : Heap}
    {store : Store Unit} {ptr : UInt64} (h : RecordStorage width heap store ptr)
    (i : Nat) (words : List UInt64) (hLength : i + words.length ≤ width)
    (back : UInt64) (hLow : 8 ≤ back.toNat) (hHigh : back.toNat ≤ 48) :
    (recordWriteValues ptr i words store).mem.read64 (ptr - back).toUInt32 =
      store.mem.read64 (ptr - back).toUInt32 := by
  have hCapacity := h.capacity
  have hBase := h.base
  have hAddress := h.address
  have hWrites := recordWriteValues_range ptr i words store (by omega)
  apply hWrites.read64
  left
  rw [headerAddress_toNat (by omega) (by omega)]
  omega

end Verified
