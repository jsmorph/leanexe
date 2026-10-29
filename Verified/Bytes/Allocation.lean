import Verified.Bytes.Represent
import Verified.Bytes.Cost
import Verified.RuntimeFacts

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

def snapshot (store : Store Unit) (root : UInt64) (count : Nat) : LeanExe.Bytes :=
  ⟨⟨Array.ofFn (n := count) fun i => store.mem.bytes (root.toNat + i)⟩⟩

@[simp] theorem snapshot_size (store : Store Unit) (root : UInt64) (count : Nat) :
    (snapshot store root count).data.size = count := Array.size_ofFn

theorem of_block {heap : Heap} {store : Store Unit} {root capacity : UInt64}
    (h : heap.Block store root capacity 1) (hMin : 8 ≤ capacity.toNat)
    (bytes : LeanExe.Bytes) (hCount : bytes.data.size ≤ capacity.toNat)
    (hContents : ∀ (i : Nat) (hi : i < bytes.data.size),
      store.mem.bytes (root.toNat + i) = bytes.data[i]) :
    Heap.Buffer heap store root bytes := by
  obtain ⟨hMagic, hReference, _, hKind, hWidth, hMask⟩ := h.fresh
  refine ⟨⟨h.base, ?_, ?_, ?_⟩, hMagic, hReference, ?_, ?_, hKind, hWidth, hMask, ?_⟩
  · rw [h.capacity_eq]; exact h.address
  · rw [h.capacity_eq]; exact h.below
  · rw [h.capacity_eq]; exact h.separate
  · rw [h.capacity_eq]; exact hMin
  · rw [h.capacity_eq]; exact hCount
  · exact hContents

theorem block_snapshot {heap : Heap} {store : Store Unit} {root capacity : UInt64}
    (h : heap.Block store root capacity 1) (hMin : 8 ≤ capacity.toNat)
    (count : Nat) (hCount : count ≤ capacity.toNat) :
    Heap.Buffer heap store root (snapshot store root count) :=
  of_block h hMin _ (by rw [snapshot_size]; exact hCount) (by
    intro i hi
    simp only [snapshot, ByteArray.getElem_eq_getElem_data, Array.getElem_ofFn])

theorem _root_.LeanExe.Pipeline.Heap.Buffer.toBlock {heap : Heap} {store : Store Unit}
    {root : UInt64} {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes)
    (hHeap : heap.At store) :
    heap.Block store root (store.mem.read64 (root - 32).toUInt32) 1 :=
  ⟨⟨h.magic, h.count, rfl, h.kind, h.width, h.childMask⟩, h.object.base,
    h.object.address, h.object.below.trans hHeap.top, h.object.below, h.object.separate⟩

theorem allocSize_minimum (count : UInt64) : 8 ≤ (allocSize count).toNat := by
  unfold allocSize
  split <;> simp_all only [UInt64.lt_iff_toNat_lt, UInt64.reduceToNat] <;> omega

theorem allocationCost_eq {count : UInt64} (hCount : count.toNat ≠ 0)
    (h32 : count.toNat ≤ 4294967296) :
    allocationCost count.toNat = allocCost (allocSize count).toNat := by
  have hRound : ((count + 7) / 8 * 8).toNat = (count.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  have hPositive : 1 ≤ (count.toNat + 7) / 8 := by omega
  have hLarge : ¬ (count + 7) / 8 * 8 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hRound]
    simp only [UInt64.reduceToNat]
    omega
  simp only [allocationCost, ite_eq_right hCount, allocSize, ite_eq_right hLarge,
    allocCost, hRound, Nat.max_eq_right hPositive]
  omega

theorem allocationCost_ge {count : Nat} (hCount : count ≠ 0) :
    48 + count ≤ allocationCost count := by
  simp only [allocationCost, ite_eq_right hCount]
  have : (count + 7) / 8 ≤ max 1 ((count + 7) / 8) := Nat.le_max_right _ _
  omega

end Verified.Bytes
