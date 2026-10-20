import Verified.TreeHeader

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

structure RecordStorage (shape : TreeShape) (heap : Heap) (store : Store Unit) (p : UInt64) :
    Prop where
  base : 4096 + 48 ≤ p.toNat
  magic : store.mem.read64 (p - 48).toUInt32 = objectMagic
  capacity : 8 * shape.fields.length ≤ capacityAt store p
  address : p.toNat + capacityAt store p < 4294967296
  below : p.toNat + capacityAt store p ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free, regionsDisjoint node.region (block store p)

theorem RecordStorage.ofHeader {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {p : UInt64} {slots : List Slot} (h : RecordHeader heap store p slots)
    (hLength : slots.length = shape.fields.length) : RecordStorage shape heap store p :=
  ⟨h.base, h.magic, by rw [← hLength]; exact h.capacity, h.address, h.below, h.separate⟩

theorem RecordStorage.ofBlock {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {p capacity stride : UInt64} (h : heap.Block store p capacity stride)
    (hRoom : 8 * shape.fields.length ≤ capacity.toNat) : RecordStorage shape heap store p := by
  have hCapacity := h.capacity_eq
  refine ⟨h.base, h.fresh.1, by rw [hCapacity]; exact hRoom,
    by rw [hCapacity]; exact h.address, by rw [hCapacity]; exact h.below, ?_⟩
  intro node hNode
  simpa only [block, hCapacity] using h.separate node hNode

theorem RecordStorage.region {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {p : UInt64} (h : RecordStorage shape heap store p) : heap.Region (block store p) := by
  have := h.base
  have := h.below
  refine ⟨?_, h.separate⟩
  simp only [block]
  omega

theorem RecordStorage.rewrite {shape : TreeShape} {heap heap' : Heap}
    {store store' : Store Unit} {p : UInt64} (h : RecordStorage shape heap store p)
    (hMagic : store'.mem.read64 (p - 48).toUInt32 = store.mem.read64 (p - 48).toUInt32)
    (hCapacity : capacityAt store' p = capacityAt store p)
    (hRegion : heap'.Region (block store p)) : RecordStorage shape heap' store' p := by
  have hBase := h.base
  refine ⟨hBase, hMagic.trans h.magic, by rw [hCapacity]; exact h.capacity,
    by rw [hCapacity]; exact h.address, ?_, ?_⟩
  · rw [hCapacity]
    have := hRegion.below
    simp only [block] at this
    omega
  · rw [block_eq hCapacity]
    exact hRegion.separate

theorem RecordStorage.write {shape : TreeShape} {heap : Heap} {store store' : Store Unit}
    {p : UInt64} {start stop : Nat} (h : RecordStorage shape heap store p)
    (hHeap : heap.At store) (hWrites : Memory.WritesRange store store' start stop)
    (hOrder : start ≤ stop)
    (hLow : p.toNat - 40 ≤ start) (hHigh : stop ≤ p.toNat + capacityAt store p)
    (hCapApart : stop ≤ p.toNat - 32 ∨ p.toNat - 24 ≤ start) :
    heap.At store' ∧ RecordStorage shape heap store' p ∧
      capacityAt store' p = capacityAt store p := by
  have hBase := h.base
  have hAddress := h.address
  have hMagic : store'.mem.read64 (p - 48).toUInt32 = store.mem.read64 (p - 48).toUInt32 := by
    apply hWrites.read64
    left
    rw [headerAddress_toNat (by change 48 ≤ p.toNat; omega) (by omega)]
    change p.toNat - 48 + 8 ≤ start
    omega
  have hCapacity : capacityAt store' p = capacityAt store p := by
    unfold capacityAt
    rw [hWrites.read64 (p - 32).toUInt32 (by
      rw [headerAddress_toNat (by change 32 ≤ p.toNat; omega) (by omega)]
      change p.toNat - 32 + 8 ≤ start ∨ stop ≤ p.toNat - 32
      omega)]
  refine ⟨hHeap.writesApart hWrites ?_, h.rewrite hMagic hCapacity h.region, hCapacity⟩
  intro node hNode
  have := h.separate node hNode
  simp only [regionsDisjoint, block] at this ⊢
  omega

theorem RecordStorage.frame {shape : TreeShape} {heap heap' : Heap}
    {store store' : Store Unit} {p : UInt64} (h : RecordStorage shape heap store p)
    (hBytes : ∀ a, p.toNat - 48 ≤ a → a < p.toNat + capacityAt store p →
      store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store p)) :
    RecordStorage shape heap' store' p ∧ capacityAt store' p = capacityAt store p := by
  have hBase := h.base
  have hAddress := h.address
  have hCapacity := capacityAt_frame (by omega) (by omega)
    (fun a hLow hHigh => hBytes a hLow (by omega))
  refine ⟨h.rewrite ?_ hCapacity hRegion, hCapacity⟩
  apply Memory.read64_congr
  intro i hi
  rw [headerAddress_toNat (by change 48 ≤ p.toNat; omega) (by omega)]
  change store'.mem.bytes (p.toNat - 48 + i) = store.mem.bytes (p.toNat - 48 + i)
  exact hBytes _ (by omega) (by omega)

theorem RecordStorage.record {shape : TreeShape} {heap : Heap} {store : Store Unit}
    {p : UInt64} {slots : List Slot} (h : RecordStorage shape heap store p)
    (hLength : slots.length = shape.fields.length)
    (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hKind : store.mem.read64 (p - 24).toUInt32 = 1)
    (hWidth : store.mem.read64 (p - 16).toUInt32 = UInt64.ofNat shape.fields.length)
    (hMask : store.mem.read64 (p - 8).toUInt32 = maskOf slots)
    (hSlots : SlotsOwned heap store p 0 slots) : NodeOwned heap store p (.record slots) := by
  refine ⟨⟨h.base, h.magic, hCount, hKind, ?_, hMask, ?_, ?_, h.address, h.below, h.separate⟩,
    hSlots⟩
  · rw [hLength]; exact hWidth
  · rw [hLength]; exact shape.short
  · rw [hLength]; exact h.capacity

#print axioms RecordStorage.write
#print axioms RecordStorage.record
#print axioms RecordStorage.frame

end Verified
