import LeanExe.Dialect.Bytes
import LeanExe.Pipeline.RuntimeSpec

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.ProofKit

structure Allocated (heap : Heap) (store : Store Unit) (root : UInt64)
    (bytes : LeanExe.Bytes) : Prop where
  object : heap.Object store root
  magic : store.mem.read64 (root - 48).toUInt32 = objectMagic
  count : store.mem.read64 (root - 40).toUInt32 = 1
  minimum : 8 ≤ capacityAt store root
  capacity : bytes.data.size ≤ capacityAt store root
  kind : store.mem.read64 (root - 24).toUInt32 = 2
  width : store.mem.read64 (root - 16).toUInt32 = 1
  childMask : store.mem.read64 (root - 8).toUInt32 = 0
  contents : ∀ (i : Nat) (hi : i < bytes.data.size),
    store.mem.bytes (root.toNat + i) = bytes.data[i]

structure Rep (heap : Heap) (store : Store Unit) (root length : UInt64)
    (bytes : LeanExe.Bytes) : Prop where
  length_eq : length.toNat = bytes.data.size
  buffer : (root = 0 ∧ bytes.data.size = 0) ∨ Allocated heap store root bytes

theorem Allocated.nonzero {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Allocated heap store root bytes) : root ≠ 0 := by
  have := h.object.base
  rintro rfl
  simp at this

theorem Allocated.region {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Allocated heap store root bytes) :
    heap.Region (root.toNat - 48, 48 + capacityAt store root) := by
  have := h.object.base
  exact ⟨by have := h.object.below; dsimp; omega, h.object.separate⟩

theorem Allocated.size_lt {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Allocated heap store root bytes) :
    bytes.data.size < 2 ^ 32 := by
  have := h.object.address
  have := h.capacity
  omega

theorem Rep.size_eq {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store root length bytes) :
    LeanExe.Bytes.size bytes = length := by
  rw [LeanExe.Bytes.size, ← h.length_eq, UInt64.ofNat_toNat]

theorem Rep.size_lt {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store root length bytes) :
    bytes.data.size < 2 ^ 32 := by
  rcases h.buffer with h | h
  · simp [h.2]
  · exact h.size_lt

theorem Allocated.read8 {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Allocated heap store root bytes) (index : UInt64)
    (hi : index.toNat < bytes.data.size) :
    store.mem.read8 (root + index).toUInt32 = bytes.data[index.toNat] := by
  have hFit := h.object.address
  have hCapacity := h.capacity
  have hSum : (root + index).toNat = root.toNat + index.toNat := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  simp only [Mem.read8, Memory.toUInt32_toNat, hSum,
    Nat.mod_eq_of_lt (by omega : root.toNat + index.toNat < 4294967296)]
  exact h.contents _ hi

theorem Allocated.get {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Allocated heap store root bytes) (index : UInt64)
    (hi : index.toNat < bytes.data.size) :
    (store.mem.read8 (root + index).toUInt32).toUInt64 = bytes.get index := by
  rw [h.read8 index hi]
  simp only [LeanExe.Bytes.get, dite_eq_left hi]

theorem Allocated.frameIn {heap heap' : Heap} {store store' : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Allocated heap store root bytes)
    (hBytes : ∀ a, root.toNat - 48 ≤ a → a < root.toNat + capacityAt store root →
      store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store root)) :
    Allocated heap' store' root bytes ∧ capacityAt store' root = capacityAt store root := by
  have hBase := h.object.base
  have hFit := h.object.address
  have hRead (offset : UInt64) (hl : 8 ≤ offset.toNat) (hh : offset.toNat ≤ 48) :
      store'.mem.read64 (root - offset).toUInt32 =
        store.mem.read64 (root - offset).toUInt32 := by
    apply Memory.read64_congr
    intro i hi
    rw [headerAddress_toNat (by omega) (by omega)]
    exact hBytes _ (by omega) (by omega)
  have hCapacity : capacityAt store' root = capacityAt store root := by
    unfold capacityAt
    rw [hRead 32 (by decide) (by decide)]
  refine ⟨?_, hCapacity⟩
  refine ⟨⟨hBase, by rw [hCapacity]; exact hFit,
      by rw [hCapacity]; have := hRegion.below; simp only [block] at this; omega,
      by rw [hCapacity]; exact hRegion.separate⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hRead 48 (by decide) (by decide)]; exact h.magic
  · rw [hRead 40 (by decide) (by decide)]; exact h.count
  · rw [hCapacity]; exact h.minimum
  · rw [hCapacity]; exact h.capacity
  · rw [hRead 24 (by decide) (by decide)]; exact h.kind
  · rw [hRead 16 (by decide) (by decide)]; exact h.width
  · rw [hRead 8 (by decide) (by decide)]; exact h.childMask
  · intro i hi
    rw [hBytes _ (by omega) (by have := h.capacity; omega)]
    exact h.contents i hi

theorem Allocated.frame {heap : Heap} {store store' : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Allocated heap store root bytes)
    (hBytes : ∀ a, root.toNat - 48 ≤ a → a < root.toNat + capacityAt store root →
      store'.mem.bytes a = store.mem.bytes a) :
    Allocated heap store' root bytes :=
  (h.frameIn hBytes h.region).1

theorem Rep.empty (heap : Heap) (store : Store Unit) :
    Rep heap store 0 0 LeanExe.Bytes.empty :=
  ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem Allocated.rep {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Allocated heap store root bytes) :
    Rep heap store root bytes.size bytes :=
  ⟨LeanExe.Bytes.size_toNat bytes (by have := h.size_lt; omega), Or.inr h⟩

theorem Rep.frame {heap : Heap} {store store' : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store root length bytes)
    (hBytes : root ≠ 0 → ∀ a, root.toNat - 48 ≤ a →
      a < root.toNat + capacityAt store root → store'.mem.bytes a = store.mem.bytes a) :
    Rep heap store' root length bytes := by
  refine ⟨h.length_eq, ?_⟩
  rcases h.buffer with h | h
  · exact Or.inl h
  · exact Or.inr (h.frame (hBytes h.nonzero))

theorem Rep.null_length {heap : Heap} {store : Store Unit} {length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store 0 length bytes) : length = 0 := by
  rcases h.buffer with hBuffer | hBuffer
  · apply UInt64.toNat_inj.mp
    rw [h.length_eq, hBuffer.2]
    rfl
  · exact False.elim (hBuffer.nonzero rfl)

theorem Allocated.release_run {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (LeanExe.Runtime.releaseFunction typeIdx))
    (env : HostEnv Unit) {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (hHeap : heap.At store) (h : Allocated heap store root bytes) :
    TerminatesWith env m 1 store [.i64 root] fun final out =>
      out = [] ∧ final = heap.releaseStore store root :=
  release_leaf_run hImports hFunc env heap store root hHeap h.object h.magic h.count h.childMask

theorem release_null_run {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (LeanExe.Runtime.releaseFunction typeIdx))
    (env : HostEnv Unit) (store : Store Unit) :
    TerminatesWith env m 1 store [.i64 0] fun final out => out = [] ∧ final = store := by
  refine TerminatesWith.of_wp_entry_for (f := LeanExe.Runtime.releaseFunction typeIdx)
    (by simpa [hImports] using hFunc) ?_ (by simp [hImports])
  simp [LeanExe.Runtime.releaseFunction, LeanExe.Runtime.releaseBody, Function.toLocals,
    Function.numParams, ValueType.zero, wp_simp]
  refine wp_iff_cons rfl ?_
  simp [wp_simp]

theorem Rep.release_run {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (LeanExe.Runtime.releaseFunction typeIdx))
    (env : HostEnv Unit) {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (hHeap : heap.At store) (h : Rep heap store root length bytes) :
    TerminatesWith env m 1 store [.i64 root] fun final out =>
      out = [] ∧ final = if root = 0 then store else heap.releaseStore store root := by
  rcases h.buffer with ⟨rfl, _⟩ | hBuffer
  · simpa using release_null_run hImports hFunc env store
  · simpa only [ite_eq_right hBuffer.nonzero] using
      hBuffer.release_run hImports hFunc env hHeap

end Verified.Bytes
