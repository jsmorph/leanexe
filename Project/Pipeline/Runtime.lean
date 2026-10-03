import Project.Runtime.FreeList
import Project.ProofKit.Array

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/-- The allocator state held in globals 0 through 5: the bump pointer `top`, the
free list, and the allocation and free counters. -/
structure Heap where
  top : UInt64
  free : List FreeNode
  allocs : UInt64
  releases : UInt64
  frees : UInt64

def Heap.globals (heap : Heap) : List Value :=
  [.i64 heap.top, .i64 (freeHead heap.free), .i64 heap.allocs, .i64 heap.frees]

/-- The allocator invariant.  The globals hold `heap`, the free list is laid out
in memory, every free block lies between the heap base at 4096 and `top`, `top`
lies inside memory, and memory has at most 65,535 pages, the maximum every compiled
module declares, so that every block ends below `2 ^ 32`. -/
structure Heap.At (heap : Heap) (store : Store Unit) : Prop where
  globals : store.globals.globals = heap.globals
  freeList : FreeListAt store.mem heap.free
  base : 4096 ≤ heap.top.toNat
  top : heap.top.toNat ≤ store.mem.pages * 65536
  pages : store.mem.pages ≤ 65535
  above : ∀ node ∈ heap.free, 4096 + 48 ≤ node.root.toNat
  below : ∀ node ∈ heap.free, node.root.toNat + node.capacity.toNat ≤ heap.top.toNat

/-- The length word and elements of `words` at `ptr`, below `top` and outside
every free block, so that no allocation can overwrite them. -/
structure Heap.Borrowed (heap : Heap) (store : Store Unit) (ptr : UInt64)
    (words : Array UInt64) : Prop where
  values : UInt64Array.At store ptr words
  below : ptr.toNat + 8 * (words.size + 1) ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free,
    regionsDisjoint (ptr.toNat, 8 * (words.size + 1)) node.region

def objectMagic : UInt64 := 5501223100278326855

/-- The payload capacity recorded in the header of the object at `ptr`. -/
def capacityAt (store : Store Unit) (ptr : UInt64) : Nat :=
  (store.mem.read64 (ptr - 32).toUInt32).toNat

/-- A runtime array object at payload pointer `ptr` holding `words`, with
reference count one, element width one, and no child pointers.  The object,
header included, lies inside the 32-bit address space, below `top`, and outside
every free block. -/
structure Heap.Owned (heap : Heap) (store : Store Unit) (ptr : UInt64)
    (words : Array UInt64) : Prop where
  values : UInt64Array.At store ptr words
  base : 4096 + 48 ≤ ptr.toNat
  magic : store.mem.read64 (ptr - 48).toUInt32 = objectMagic
  count : store.mem.read64 (ptr - 40).toUInt32 = 1
  capacity : 8 * (words.size + 1) ≤ capacityAt store ptr
  kind : store.mem.read64 (ptr - 24).toUInt32 = 2
  width : store.mem.read64 (ptr - 16).toUInt32 = 1
  childMask : store.mem.read64 (ptr - 8).toUInt32 = 0
  address : ptr.toNat + capacityAt store ptr < 4294967296
  below : ptr.toNat + capacityAt store ptr ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free,
    regionsDisjoint node.region (ptr.toNat - 48, 48 + capacityAt store ptr)

/-- A region below `top` and outside every free block, which allocation leaves alone. -/
structure Heap.Region (heap : Heap) (r : Nat × Nat) : Prop where
  below : r.1 + r.2 ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free, regionsDisjoint node.region r

/-- What a step from `heap` at `initial` to `heap'` at `store` leaves of the regions of `heap`
that lie apart from the blocks `gone`: each keeps its bytes, is a region of `heap'`, and lies
apart from each of the blocks `fresh`. -/
def Heap.Keeps (heap : Heap) (initial : Store Unit) (gone : List (Nat × Nat)) (heap' : Heap)
    (store : Store Unit) (fresh : List (Nat × Nat)) : Prop :=
  ∀ r, heap.Region r → 0 < r.2 → (∀ b ∈ gone, regionsDisjoint r b) →
    (∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a) ∧
      heap'.Region r ∧ ∀ b ∈ fresh, regionsDisjoint r b

/-- A step that changes nothing keeps every region. -/
theorem Heap.Keeps.refl (heap : Heap) (store : Store Unit) (gone : List (Nat × Nat)) :
    heap.Keeps store gone heap store [] :=
  fun _ hr _ _ => ⟨fun _ _ _ => rfl, hr, fun _ hb => nomatch hb⟩

/-- Two steps in a row, the second consuming only blocks that the first leaves fresh or that
the first already consumes. -/
theorem Heap.Keeps.trans {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {gone gone2 fresh1 fresh2 : List (Nat × Nat)}
    (h1 : heap.Keeps initial gone heap1 store1 fresh1)
    (h2 : heap1.Keeps store1 gone2 heap2 store2 fresh2)
    (hGone : ∀ r, (∀ b ∈ gone, regionsDisjoint r b) → (∀ b ∈ fresh1, regionsDisjoint r b) →
      ∀ b ∈ gone2, regionsDisjoint r b) :
    heap.Keeps initial gone heap2 store2 fresh2 := fun r hr hpos hApart => by
  obtain ⟨hBytes1, hRegion1, hFresh1⟩ := h1 r hr hpos hApart
  obtain ⟨hBytes2, hRegion2, hFresh2⟩ := h2 r hRegion1 hpos (hGone r hApart hFresh1)
  exact ⟨fun a hl hh => (hBytes2 a hl hh).trans (hBytes1 a hl hh), hRegion2, hFresh2⟩

/-- Two steps in a row, as in `Heap.Keeps.trans`, leave every kept region apart from the blocks
that either step leaves fresh. -/
theorem Heap.Keeps.transBoth {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {gone gone2 fresh1 fresh2 : List (Nat × Nat)}
    (h1 : heap.Keeps initial gone heap1 store1 fresh1)
    (h2 : heap1.Keeps store1 gone2 heap2 store2 fresh2)
    (hGone : ∀ r, (∀ b ∈ gone, regionsDisjoint r b) → (∀ b ∈ fresh1, regionsDisjoint r b) →
      ∀ b ∈ gone2, regionsDisjoint r b) :
    heap.Keeps initial gone heap2 store2 (fresh1 ++ fresh2) := fun r hr hpos hApart => by
  obtain ⟨hBytes1, hRegion1, hFresh1⟩ := h1 r hr hpos hApart
  obtain ⟨hBytes2, hRegion2, hFresh2⟩ := h2 r hRegion1 hpos (hGone r hApart hFresh1)
  refine ⟨fun a hl hh => (hBytes2 a hl hh).trans (hBytes1 a hl hh), hRegion2, fun b hb => ?_⟩
  rcases List.mem_append.mp hb with hb | hb
  · exact hFresh1 b hb
  · exact hFresh2 b hb

/-- A step keeps the regions apart from more blocks, and leaves them apart from fewer. -/
theorem Heap.Keeps.mono {heap heap' : Heap} {initial store : Store Unit}
    {gone gone' fresh fresh' : List (Nat × Nat)} (h : heap.Keeps initial gone heap' store fresh)
    (hGone : ∀ b ∈ gone, b ∈ gone') (hFresh : ∀ b ∈ fresh', b ∈ fresh) :
    heap.Keeps initial gone' heap' store fresh' := fun r hr hpos hApart => by
  obtain ⟨hBytes, hRegion, hApartFresh⟩ := h r hr hpos fun b hb => hApart b (hGone b hb)
  exact ⟨hBytes, hRegion, fun b hb => hApartFresh b (hFresh b hb)⟩

end Project.Pipeline
