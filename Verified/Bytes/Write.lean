import Verified.Bytes.Allocation
import Verified.LocalFrame

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit

def writeByte (store : Store Unit) (root index : UInt64) (value : UInt8) : Store Unit :=
  { store with mem := store.mem.write8 (root + index).toUInt32 value }

def updated (bytes : LeanExe.Bytes) (index : Nat) (value : UInt8)
    (h : index < bytes.data.size) : LeanExe.Bytes :=
  ⟨bytes.data.set index value h⟩

@[simp] theorem updated_size (bytes : LeanExe.Bytes) (index : Nat) (value : UInt8)
    (h : index < bytes.data.size) : (updated bytes index value h).data.size = bytes.data.size :=
  Array.size_set (h := h)

theorem _root_.LeanExe.Pipeline.Heap.Buffer.write_within {heap : Heap} {store : Store Unit}
    {root : UInt64} {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) (index : UInt64)
    (hi : index.toNat < bytes.data.size) (value : UInt8) :
    WritesWithin store (writeByte store root index value) root.toNat (capacityAt store root) := by
  refine ⟨rfl, rfl, ?_⟩
  intro address hOutside
  have hAddress := h.index_address index hi
  have hCapacity := h.capacity
  simp only [writeByte, Mem.write8]
  rw [ite_eq_right (by rw [hAddress]; omega)]

theorem _root_.LeanExe.Pipeline.Heap.Buffer.write {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) (hHeap : heap.At store)
    (index : UInt64) (hi : index.toNat < bytes.data.size) (value : UInt8) :
    heap.At (writeByte store root index value) ∧
      Heap.Buffer heap (writeByte store root index value) root
        (updated bytes index.toNat value hi) := by
  have hBlock := h.toBlock hHeap
  have hWrites := h.write_within index hi value
  refine ⟨hHeap.writesWithin hBlock hWrites,
    of_block (hBlock.writesWithin hWrites) h.minimum _ ?_ ?_⟩
  · rw [updated_size]
    exact h.capacity
  · intro j hj
    rw [updated_size] at hj
    have hAddress := h.index_address index hi
    by_cases hij : index.toNat = j
    · subst j
      simp only [writeByte, Mem.write8, hAddress, updated,
        ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set,
        ite_true, eq_self]
    · have hji : j ≠ index.toNat := Ne.symm hij
      simp only [writeByte, Mem.write8, hAddress, updated,
        ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set,
        Nat.add_left_cancel_iff, hij, hji, ite_false]
      exact h.contents j hj

theorem _root_.LeanExe.Pipeline.Heap.Buffer.write_range {heap : Heap} {store : Store Unit}
    {root : UInt64} {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) (index : UInt64)
    (hi : index.toNat < bytes.data.size) (value : UInt8) :
    Memory.WritesRange store (writeByte store root index value)
      root.toNat (root.toNat + bytes.data.size) :=
  Memory.WritesRange.write8 _ _ _ _ _
    (by rw [h.index_address index hi]; omega)
    (by rw [h.index_address index hi]; omega)

theorem _root_.LeanExe.Pipeline.Heap.Buffer.capacity_writesRange {heap : Heap}
    {store store' : Store Unit} {root : UInt64} {bytes : LeanExe.Bytes} {stop : Nat}
    (h : Heap.Buffer heap store root bytes)
    (hWrites : Memory.WritesRange store store' root.toNat stop) :
    capacityAt store' root = capacityAt store root := by
  unfold capacityAt
  apply congrArg UInt64.toNat
  apply hWrites.read64
  left
  have hBase := h.object.base
  have hAddress := h.object.address
  rw [headerAddress_toNat (by simp; omega) (by omega)]
  simp only [UInt64.reduceToNat]
  omega

theorem _root_.LeanExe.Pipeline.Heap.Buffer.write_step {heap : Heap} {store : Store Unit}
    {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) (hHeap : heap.At store)
    (index : UInt64) (hi : index.toNat < bytes.data.size) (value : UInt8) :
    Step heap store (fun r => LeanExe.Runtime.regionsDisjoint r (block store root))
      heap (writeByte store root index value) [] ∧
      capacityAt (writeByte store root index value) root = capacityAt store root := by
  have hWrite := h.write_range index hi value
  have hCapacity := h.capacity
  have hBase := h.object.base
  have hBlock := h.toBlock hHeap
  refine ⟨Step.ofWritesRange (h.write hHeap index hi value).1 hWrite
    (by simp only [block]; omega) (by simp only [block]; omega), ?_⟩
  exact ((hBlock.writesWithin (h.write_within index hi value)).capacity_eq).trans
    hBlock.capacity_eq.symm

theorem wp_store {m : Module} {host : HostEnv Unit} {heap : Heap} {store : Store Unit}
    {s : Locals} {root index : UInt64} {bytes : LeanExe.Bytes} {value : UInt32}
    {vs : List Value} {rest : Program} {Q : Assertion Unit}
    (hHeap : heap.At store) (h : Heap.Buffer heap store root bytes)
    (hi : index.toNat < bytes.data.size)
    (hNext : wp m rest Q (writeByte store root index value.toUInt8)
      { s with values := vs } host) :
    wp m (.store8 0 :: rest) Q store
      { s with values := .i32 value :: .i32 (root + index).toUInt32 :: vs } host := by
  have hAddress := h.index_address index hi
  have hCapacity := h.capacity
  have hBelow := h.object.below
  have hTop := hHeap.top
  simp only [wp_store8_cons, UInt32.toNat_zero, Nat.add_zero, UInt32.add_zero]
  rw [ite_eq_right (by rw [hAddress]; omega)]
  exact hNext

end Verified.Bytes
