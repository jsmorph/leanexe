import Verified.Bytes.Memory
import LeanExe.Pipeline.RuntimeSpec
import LeanExe.Pipeline.Bytes

namespace Verified.Bytes

open Wasm LeanExe.Pipeline LeanExe.Pipeline.Bytes LeanExe.ProofKit

theorem _root_.LeanExe.Pipeline.Heap.Buffer.payload_region {heap : Heap} {store : Store Unit}
    {root : UInt64} {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) :
    heap.Region (root.toNat, bytes.data.size) := by
  have hBase := h.object.base
  have hCapacity := h.capacity
  refine ⟨by have := h.object.below; omega, ?_⟩
  intro node hNode
  have hApart := h.object.separate node hNode
  simp only [LeanExe.Runtime.regionsDisjoint] at hApart ⊢
  omega

theorem _root_.LeanExe.Pipeline.Heap.Buffer.size_lt {heap : Heap} {store : Store Unit}
    {root : UInt64} {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) :
    bytes.data.size < 2 ^ 32 := by
  have := h.object.address
  have := h.capacity
  omega

theorem _root_.LeanExe.Pipeline.Bytes.Rep.size_eq
    {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store root length bytes) :
    LeanExe.Bytes.size bytes = length := by
  rw [LeanExe.Bytes.size, ← h.length_eq, UInt64.ofNat_toNat]

theorem _root_.LeanExe.Pipeline.Bytes.Rep.size_lt
    {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store root length bytes) :
    bytes.data.size < 2 ^ 32 := by
  rcases h.buffer with h | h
  · simp [h.2]
  · exact h.size_lt

theorem _root_.LeanExe.Pipeline.Heap.Buffer.index_address {heap : Heap} {store : Store Unit}
    {root : UInt64} {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) (index : UInt64)
    (hi : index.toNat < bytes.data.size) :
    (root + index).toUInt32.toNat = root.toNat + index.toNat := by
  apply Verified.Bytes.index_address root index bytes.data.size _ hi
  have := h.object.address
  have := h.capacity
  omega

theorem _root_.LeanExe.Pipeline.Heap.Buffer.toAt {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) (hHeap : heap.At store) :
    At store.mem root bytes := by
  have hCapacity := h.capacity
  refine ⟨by have := h.object.address; omega, ?_, h.contents⟩
  have := h.object.below
  have := hHeap.top
  omega

theorem _root_.LeanExe.Pipeline.Heap.Buffer.read8 {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) (index : UInt64)
    (hi : index.toNat < bytes.data.size) :
    store.mem.read8 (root + index).toUInt32 = bytes.data[index.toNat] := by
  rw [Mem.read8, h.index_address index hi]
  exact h.contents _ hi

theorem _root_.LeanExe.Pipeline.Heap.Buffer.get {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) (index : UInt64)
    (hi : index.toNat < bytes.data.size) :
    (store.mem.read8 (root + index).toUInt32).toUInt64 = bytes.get index := by
  rw [h.read8 index hi]
  simp only [LeanExe.Bytes.get, dite_eq_left hi]

theorem _root_.LeanExe.Pipeline.Bytes.Rep.empty (heap : Heap) (store : Store Unit) :
    Rep heap store 0 0 LeanExe.Bytes.empty :=
  ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩

theorem _root_.LeanExe.Pipeline.Heap.Buffer.rep {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (h : Heap.Buffer heap store root bytes) :
    Rep heap store root bytes.size bytes :=
  ⟨LeanExe.Bytes.size_toNat bytes (by have := h.size_lt; omega), Or.inr h⟩

theorem _root_.LeanExe.Pipeline.Bytes.Rep.frame
    {heap : Heap} {store store' : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store root length bytes)
    (hBytes : root ≠ 0 → ∀ a, root.toNat - 48 ≤ a →
      a < root.toNat + capacityAt store root → store'.mem.bytes a = store.mem.bytes a) :
    Rep heap store' root length bytes := by
  refine ⟨h.length_eq, ?_⟩
  rcases h.buffer with h | h
  · exact Or.inl h
  · exact Or.inr (h.frame (hBytes h.nonzero))

theorem _root_.LeanExe.Pipeline.Bytes.Rep.null_length
    {heap : Heap} {store : Store Unit} {length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store 0 length bytes) : length = 0 := by
  rcases h.buffer with hBuffer | hBuffer
  · apply UInt64.toNat_inj.mp
    rw [h.length_eq, hBuffer.2]
    rfl
  · exact False.elim (hBuffer.nonzero rfl)

theorem _root_.LeanExe.Pipeline.Bytes.Rep.toAt
    {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store root length bytes) (hHeap : heap.At store) :
    At store.mem root bytes := by
  rcases h.buffer with ⟨rfl, hEmpty⟩ | hBuffer
  · exact ⟨by simp [hEmpty], by simp [hEmpty], fun i hi => by omega⟩
  · exact hBuffer.toAt hHeap

theorem _root_.LeanExe.Pipeline.Bytes.Rep.payload_region
    {heap : Heap} {store : Store Unit} {root length : UInt64}
    {bytes : LeanExe.Bytes} (h : Rep heap store root length bytes) :
    heap.Region (root.toNat, bytes.data.size) := by
  rcases h.buffer with ⟨rfl, hEmpty⟩ | hBuffer
  · exact ⟨by simp [hEmpty], fun node _ => by
      simp [LeanExe.Runtime.regionsDisjoint, hEmpty]⟩
  · exact hBuffer.payload_region

theorem _root_.LeanExe.Pipeline.Heap.Buffer.release_run {m : Module} {typeIdx : Nat}
    (hImports : m.imports = [])
    (hFunc : m.funcs[1]? = some (LeanExe.Runtime.releaseFunction typeIdx))
    (env : HostEnv Unit) {heap : Heap} {store : Store Unit} {root : UInt64}
    {bytes : LeanExe.Bytes} (hHeap : heap.At store) (h : Heap.Buffer heap store root bytes) :
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

theorem _root_.LeanExe.Pipeline.Bytes.Rep.release_run
    {m : Module} {typeIdx : Nat} (hImports : m.imports = [])
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
