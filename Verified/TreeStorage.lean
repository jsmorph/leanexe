import Verified.TreeHeader

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.ProofKit LeanExe.Runtime

structure RecordStorage (width : Nat) (heap : Heap) (store : Store Unit) (p : UInt64) :
    Prop where
  base : 4096 + 48 ≤ p.toNat
  magic : store.mem.read64 (p - 48).toUInt32 = objectMagic
  capacity : 8 * width ≤ capacityAt store p
  address : p.toNat + capacityAt store p < 4294967296
  below : p.toNat + capacityAt store p ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free, regionsDisjoint node.region (block store p)

theorem RecordStorage.ofHeader {width : Nat} {heap : Heap} {store : Store Unit}
    {p : UInt64} {slots : List Slot} (h : RecordHeader heap store p slots)
    (hLength : slots.length = width) : RecordStorage width heap store p :=
  ⟨h.base, h.magic, by rw [← hLength]; exact h.capacity, h.address, h.below, h.separate⟩

theorem RecordStorage.ofBlock {width : Nat} {heap : Heap} {store : Store Unit}
    {p capacity stride : UInt64} (h : heap.Block store p capacity stride)
    (hRoom : 8 * width ≤ capacity.toNat) : RecordStorage width heap store p := by
  have hCapacity := h.capacity_eq
  refine ⟨h.base, h.fresh.1, by rw [hCapacity]; exact hRoom,
    by rw [hCapacity]; exact h.address, by rw [hCapacity]; exact h.below, ?_⟩
  intro node hNode
  simpa only [block, hCapacity] using h.separate node hNode

theorem RecordStorage.region {width : Nat} {heap : Heap} {store : Store Unit}
    {p : UInt64} (h : RecordStorage width heap store p) : heap.Region (block store p) := by
  have := h.base
  have := h.below
  refine ⟨?_, h.separate⟩
  simp only [block]
  omega

theorem RecordStorage.rewrite {width : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {p : UInt64} (h : RecordStorage width heap store p)
    (hMagic : store'.mem.read64 (p - 48).toUInt32 = store.mem.read64 (p - 48).toUInt32)
    (hCapacity : capacityAt store' p = capacityAt store p)
    (hRegion : heap'.Region (block store p)) : RecordStorage width heap' store' p := by
  have hBase := h.base
  refine ⟨hBase, hMagic.trans h.magic, by rw [hCapacity]; exact h.capacity,
    by rw [hCapacity]; exact h.address, ?_, ?_⟩
  · rw [hCapacity]
    have := hRegion.below
    simp only [block] at this
    omega
  · rw [block_eq hCapacity]
    exact hRegion.separate

theorem RecordStorage.write {width : Nat} {heap : Heap} {store store' : Store Unit}
    {p : UInt64} {start stop : Nat} (h : RecordStorage width heap store p)
    (hHeap : heap.At store) (hWrites : Memory.WritesRange store store' start stop)
    (hOrder : start ≤ stop)
    (hLow : p.toNat - 40 ≤ start) (hHigh : stop ≤ p.toNat + capacityAt store p)
    (hCapApart : stop ≤ p.toNat - 32 ∨ p.toNat - 24 ≤ start) :
    heap.At store' ∧ RecordStorage width heap store' p ∧
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

theorem RecordStorage.frame {width : Nat} {heap heap' : Heap}
    {store store' : Store Unit} {p : UInt64} (h : RecordStorage width heap store p)
    (hBytes : ∀ a, p.toNat - 48 ≤ a → a < p.toNat + capacityAt store p →
      store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store p)) :
    RecordStorage width heap' store' p ∧ capacityAt store' p = capacityAt store p := by
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

def recordHeaderWrite (store : Store Unit) (p back value : UInt64) : Store Unit :=
  { store with mem := store.mem.write64 (p - back).toUInt32 value }

theorem RecordStorage.writeHeader {width : Nat} {heap : Heap} {store : Store Unit}
    {p back value : UInt64} (h : RecordStorage width heap store p) (hHeap : heap.At store)
    (hBack : back = 8 ∨ back = 16 ∨ back = 24 ∨ back = 40) :
    heap.At (recordHeaderWrite store p back value) ∧
      RecordStorage width heap (recordHeaderWrite store p back value) p ∧
      capacityAt (recordHeaderWrite store p back value) p = capacityAt store p := by
  have hBase := h.base
  have hAddress := h.address
  have hBounds : 8 ≤ back.toNat ∧ back.toNat ≤ 40 ∧ (back.toNat ≤ 24 ∨ back.toNat = 40) := by
    rcases hBack with rfl | rfl | rfl | rfl <;> decide
  have hAddr : (p - back).toUInt32.toNat = p.toNat - back.toNat :=
    headerAddress_toNat (by omega) (by omega)
  apply h.write hHeap
    (Memory.WritesRange.write64 _ _ _ (p.toNat - back.toNat) (p.toNat - back.toNat + 8)
      (by rw [hAddr]) (by rw [hAddr]))
  all_goals omega

theorem RecordStorage.writeHeader_range {width : Nat} {heap : Heap} {store : Store Unit}
    {p back value : UInt64} (h : RecordStorage width heap store p)
    (hBack : back = 8 ∨ back = 16 ∨ back = 24 ∨ back = 40) :
    Memory.WritesRange store (recordHeaderWrite store p back value) (p.toNat - 40) p.toNat := by
  have hBase := h.base
  have hAddress := h.address
  have hBounds : 8 ≤ back.toNat ∧ back.toNat ≤ 40 := by
    rcases hBack with rfl | rfl | rfl | rfl <;> decide
  have hAddr := headerAddress_toNat (ptr := p) (k := back) (by omega) (by omega)
  exact Memory.WritesRange.write64 _ _ _ _ _ (by rw [hAddr]; omega) (by rw [hAddr]; omega)

theorem RecordStorage.readHeader_write {width : Nat} {heap : Heap} {store : Store Unit}
    {p back other value : UInt64} (h : RecordStorage width heap store p)
    (hBack : back = 8 ∨ back = 16 ∨ back = 24 ∨ back = 40)
    (hOther : other = 8 ∨ other = 16 ∨ other = 24 ∨ other = 40) (hNe : back ≠ other) :
    (recordHeaderWrite store p back value).mem.read64 (p - other).toUInt32 =
      store.mem.read64 (p - other).toUInt32 := by
  have hBase := h.base
  have hAddress := h.address
  have hb : back.toNat ≤ 40 := by rcases hBack with rfl | rfl | rfl | rfl <;> decide
  have ho : other.toNat ≤ 40 := by rcases hOther with rfl | rfl | rfl | rfl <;> decide
  have hAddr (k : UInt64) (hk : k.toNat ≤ 40) :
      (p - k).toUInt32.toNat = p.toNat - k.toNat :=
    headerAddress_toNat (by omega) (by omega)
  have hWrites : Memory.WritesRange store (recordHeaderWrite store p back value)
      (p.toNat - back.toNat) (p.toNat - back.toNat + 8) :=
    Memory.WritesRange.write64 _ _ _ _ _ (by rw [hAddr back hb]) (by rw [hAddr back hb])
  apply hWrites.read64
  rw [hAddr other ho]
  rcases hBack with rfl | rfl | rfl | rfl <;>
    rcases hOther with rfl | rfl | rfl | rfl <;> simp_all [UInt64.reduceToNat] <;> omega

theorem RecordStorage.record {width : Nat} {heap : Heap} {store : Store Unit}
    {p : UInt64} {slots : List Slot} (h : RecordStorage width heap store p)
    (hLength : slots.length = width)
    (hCount : store.mem.read64 (p - 40).toUInt32 = 1)
    (hKind : store.mem.read64 (p - 24).toUInt32 = 1)
    (hWidth : store.mem.read64 (p - 16).toUInt32 = UInt64.ofNat width)
    (hMask : store.mem.read64 (p - 8).toUInt32 = maskOf slots)
    (hShort : width ≤ 64) (hSlots : SlotsOwned heap store p 0 slots) :
    NodeOwned heap store p (.record slots) := by
  refine ⟨⟨h.base, h.magic, hCount, hKind, ?_, hMask, ?_, ?_, h.address, h.below, h.separate⟩,
    hSlots⟩
  · rw [hLength]; exact hWidth
  · rw [hLength]; exact hShort
  · rw [hLength]; exact h.capacity

#print axioms RecordStorage.write
#print axioms RecordStorage.record
#print axioms RecordStorage.frame
#print axioms RecordStorage.writeHeader
#print axioms RecordStorage.readHeader_write

end Verified
