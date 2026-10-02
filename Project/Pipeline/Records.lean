import Project.Pipeline.Allocation
import Project.Pipeline.Implements
import Project.ProofKit.MemoryFrame

/-!
Facts about records on the heap.  A region below `top` and outside every free block keeps
its bytes through an allocation and lies apart from the new block.  An owned record keeps
its header and slots, and an owned value its records, when the bytes of their blocks do.
-/

namespace Project.Pipeline

open Wasm Project.Runtime Project.ProofKit

/-- A region below `top` and outside every free block, which allocation leaves alone. -/
structure Heap.Region (heap : Heap) (r : Nat × Nat) : Prop where
  below : r.1 + r.2 ≤ heap.top.toNat
  separate : ∀ node ∈ heap.free, regionsDisjoint node.region r

/-- An allocation leaves the bytes of a region, which stays a region and lies apart from the
new block. -/
theorem Heap.Region.allocate {heap : Heap} {store : Store Unit} {r : Nat × Nat}
    {need : UInt64} (stride : UInt64) (h : heap.Region r) (hHeap : heap.At store)
    (hFits : heap.Fits need) :
    (heap.allocate need).Region r ∧
      (∀ a, r.1 ≤ a → a < r.1 + r.2 →
        (heap.allocateStore store need stride).mem.bytes a = store.mem.bytes a) ∧
      regionsDisjoint r ((FixedArrayAllocate.root heap.top need heap.free).toNat - 48,
        48 + (allocatedCapacity need heap.free).toNat) := by
  have hBump : takeFirstFitFrom 0 need heap.free = none →
      heap.top.toNat + 48 + need.toNat ≤ 4294967296 := fun h => by have := hFits h; omega
  have hBelow := h.below
  refine ⟨⟨?_, fun node hNode => regionsDisjoint_symm (allocatedNodes_apart hHeap.freeList
      (fun n hn => regionsDisjoint_symm (h.separate n hn)) node hNode)⟩,
    fun a hLow hHigh => allocated_bytes_outside store heap.top need stride heap.free r.1 r.2
      hHeap.freeList (fun node hNode => regionsDisjoint_symm (h.separate node hNode)) hBelow
      hBump a hLow hHigh, ?_⟩
  · show r.1 + r.2 ≤ (allocatedTop heap.top need heap.free).toNat
    rw [allocatedTop_toNat heap.top need heap.free hBump]
    split <;> omega
  cases hTake : takeFirstFitFrom 0 need heap.free with
  | some choice =>
    have := h.separate _ (takeFirstFitFrom_some_mem hTake)
    have hWithin := allocated_within (base := heap.top) hHeap.freeList hTake
    simp only [FreeNode.region, regionsDisjoint] at this ⊢
    omega
  | none =>
    have h48 : (48 : UInt64).toNat = 48 := rfl
    have := hHeap.top
    have := hHeap.pages
    simp only [FixedArrayAllocate.root, allocatedCapacity, hTake, regionsDisjoint,
      UInt64.toNat_add, h48, Nat.reducePow]
    omega

/-- Slot `i` of a record lies `8 * i` bytes after its pointer. -/
theorem slotAddress_toNat {p : UInt64} {i : Nat} (h : p.toNat + 8 * i < 4294967296) :
    (slotAddress p i).toNat = p.toNat + 8 * i := by
  unfold slotAddress
  rw [Memory.toUInt32_toNat, UInt64.toNat_add, UInt64.toNat_ofNat']
  omega

/-- A record keeps its header and capacity when the bytes of its block do, and it stays
owned in any heap whose free blocks and `top` leave its block alone. -/
theorem RecordHeader.frame {heap heap' : Heap} {store store' : Store Unit} {p : UInt64}
    {slots : List Slot} (h : RecordHeader heap store p slots)
    (hBytes : ∀ a, p.toNat - 48 ≤ a → a < p.toNat + capacityAt store p →
      store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store p)) :
    RecordHeader heap' store' p slots ∧ capacityAt store' p = capacityAt store p := by
  have hBase := h.base
  have hAddress := h.address
  have hHeader : ∀ k : UInt64, k.toNat ≤ 48 → 8 ≤ k.toNat →
      store'.mem.read64 (p - k).toUInt32 = store.mem.read64 (p - k).toUInt32 :=
    fun k hk h8 => Memory.read64_congr _ fun i hi => by
      rw [headerAddress_toNat (by omega) (by omega)]
      exact hBytes _ (by omega) (by omega)
  have hCapacity : capacityAt store' p = capacityAt store p := by
    unfold capacityAt
    rw [hHeader 32 (by decide) (by decide)]
  have hBelow := hRegion.below
  have hSeparate := hRegion.separate
  simp only [block] at hBelow hSeparate
  refine ⟨⟨hBase, ?_, ?_, ?_, ?_, ?_, h.short, ?_, ?_, ?_, ?_⟩, hCapacity⟩
  · rw [hHeader 48 (by decide) (by decide)]; exact h.magic
  · rw [hHeader 40 (by decide) (by decide)]; exact h.count
  · rw [hHeader 24 (by decide) (by decide)]; exact h.kind
  · rw [hHeader 16 (by decide) (by decide)]; exact h.width
  · rw [hHeader 8 (by decide) (by decide)]; exact h.mask
  · rw [hCapacity]; exact h.capacity
  · rw [hCapacity]; exact hAddress
  · rw [hCapacity]; omega
  · rw [hCapacity]; exact hSeparate

mutual
/-- An owned value keeps its records and their blocks when the bytes of those blocks are
unchanged and every block stays a region of the new heap. -/
theorem NodeOwned.frame {heap heap' : Heap} {store store' : Store Unit} :
    ∀ (p : UInt64) (n : Node), NodeOwned heap store p n →
      (∀ b ∈ n.blocks store p, (∀ a, b.1 ≤ a → a < b.1 + b.2 →
        store'.mem.bytes a = store.mem.bytes a) ∧ heap'.Region b) →
      NodeOwned heap' store' p n ∧ n.blocks store' p = n.blocks store p
  | _, .null, h, _ => ⟨h, rfl⟩
  | p, .record slots, ⟨hHead, hSlots⟩, hBlocks => by
      have hFirst := hBlocks (block store p) List.mem_cons_self
      obtain ⟨hHead', hCapacity⟩ := hHead.frame
        (fun a hLow hHigh => hFirst.1 a (by simp only [block]; omega)
          (by simp only [block]; omega)) hFirst.2
      have hCap := hHead.capacity
      have hAddress := hHead.address
      obtain ⟨hSlots', hRest⟩ := SlotsOwned.frame p 0 slots hSlots (by omega)
        (fun a hLow hHigh => hFirst.1 a (by simp only [block]; omega)
          (by simp only [block]; omega))
        (fun b hb => hBlocks b (List.mem_cons_of_mem _ hb))
      exact ⟨⟨hHead', hSlots'⟩, by simp only [Node.blocks, block_eq hCapacity, hRest]⟩

/-- The slots from `i` on of an owned record keep their words and children when the bytes
of the record's payload and of the children's blocks are unchanged. -/
theorem SlotsOwned.frame {heap heap' : Heap} {store store' : Store Unit} :
    ∀ (p : UInt64) (i : Nat) (slots : List Slot), SlotsOwned heap store p i slots →
      p.toNat + 8 * (i + slots.length) < 4294967296 →
      (∀ a, p.toNat ≤ a → a < p.toNat + 8 * (i + slots.length) →
        store'.mem.bytes a = store.mem.bytes a) →
      (∀ b ∈ slotsBlocks store p i slots, (∀ a, b.1 ≤ a → a < b.1 + b.2 →
        store'.mem.bytes a = store.mem.bytes a) ∧ heap'.Region b) →
      SlotsOwned heap' store' p i slots ∧ slotsBlocks store' p i slots = slotsBlocks store p i slots
  | _, _, [], _, _, _, _ => ⟨trivial, rfl⟩
  | p, i, .word w :: rest, ⟨hWord, hRest⟩, hAddress, hBytes, hBlocks => by
      simp only [List.length_cons] at hAddress hBytes
      have hRead : store'.mem.read64 (slotAddress p i) = store.mem.read64 (slotAddress p i) :=
        Memory.read64_congr _ fun k hk => by
          rw [slotAddress_toNat (by omega)]
          exact hBytes _ (by omega) (by omega)
      obtain ⟨hRest', hBlocks'⟩ := SlotsOwned.frame p (i + 1) rest hRest (by omega)
        (fun a hLow hHigh => hBytes a hLow (by omega)) hBlocks
      exact ⟨⟨hRead.trans hWord, hRest'⟩, hBlocks'⟩
  | p, i, .child n :: rest, ⟨hChild, hRest⟩, hAddress, hBytes, hBlocks => by
      simp only [List.length_cons] at hAddress hBytes
      have hRead : store'.mem.read64 (slotAddress p i) = store.mem.read64 (slotAddress p i) :=
        Memory.read64_congr _ fun k hk => by
          rw [slotAddress_toNat (by omega)]
          exact hBytes _ (by omega) (by omega)
      simp only [slotsBlocks, List.mem_append] at hBlocks
      obtain ⟨hChild', hChildBlocks⟩ := NodeOwned.frame _ n hChild
        (fun b hb => hBlocks b (.inl hb))
      obtain ⟨hRest', hRestBlocks⟩ := SlotsOwned.frame p (i + 1) rest hRest (by omega)
        (fun a hLow hHigh => hBytes a hLow (by omega)) (fun b hb => hBlocks b (.inr hb))
      refine ⟨⟨by rw [hRead]; exact hChild', hRest'⟩, ?_⟩
      simp only [slotsBlocks, hRead, hChildBlocks, hRestBlocks]
end

/-- Writes apart from every free block keep the allocator invariant. -/
theorem Heap.At.writesApart {heap : Heap} {store store' : Store Unit} {start stop : Nat}
    (h : heap.At store) (hWrites : Memory.WritesRange store store' start stop)
    (hApart : ∀ node ∈ heap.free, regionsDisjoint node.region (start, stop - start)) :
    heap.At store' := by
  have hGlobals : store'.globals = store.globals := by rw [hWrites.1]
  refine ⟨by rw [hGlobals]; exact h.globals, ?_, h.base, by rw [hWrites.2.1]; exact h.top,
    by rw [hWrites.2.1]; exact h.pages, h.above, h.below⟩
  apply FreeListMemory.frame_headers h.freeList (by rw [hWrites.2.1])
  intro node hNode address hLow hHigh
  apply hWrites.2.2
  have hSeparate := hApart node hNode
  have := h.above node hNode
  simp only [regionsDisjoint, FreeNode.region] at hSeparate
  omega

/-- What allocating a record at `ptr` and filling it leaves, with `heap'` the heap after the
allocation: the allocator invariant; a header with kind 1, the number of words, and the child
mask `mask`; the words in the slots; and every region of the old heap with its bytes, still
a region, and apart from the new block. -/
structure Heap.NewRecord (heap : Heap) (initial : Store Unit) (heap' : Heap) (store : Store Unit)
    (ptr : UInt64) (words : List UInt64) (mask : UInt64) : Prop where
  at_ : heap'.At store
  header : ∀ slots : List Slot, slots.length = words.length → maskOf slots = mask →
    RecordHeader heap' store ptr slots
  slots : ∀ i (h : i < words.length), store.mem.read64 (slotAddress ptr i) = words[i]
  region : ∀ r, heap.Region r →
    (∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a) ∧
      heap'.Region r ∧ regionsDisjoint r (block store ptr)
  pages : initial.mem.pages ≤ store.mem.pages
  caps : store.memoryCaps = initial.memoryCaps

/-- A borrowed array occupies a region of the heap. -/
theorem Heap.Borrowed.region {heap : Heap} {store : Store Unit} {p : UInt64}
    {ws : Array UInt64} (h : heap.Borrowed store p ws) :
    heap.Region (p.toNat, 8 * (ws.size + 1)) :=
  ⟨h.below, fun node hNode => regionsDisjoint_symm (h.separate node hNode)⟩

/-- An owned array's block is a region of the heap. -/
theorem Heap.Owned.region {heap : Heap} {store : Store Unit} {p : UInt64} {ws : Array UInt64}
    (h : heap.Owned store p ws) : heap.Region (block store p) := by
  have := h.below
  have := h.base
  exact ⟨by simp only [block]; omega, h.separate⟩

/-- An owned record's block is a region of the heap. -/
theorem RecordHeader.region {heap : Heap} {store : Store Unit} {p : UInt64} {slots : List Slot}
    (h : RecordHeader heap store p slots) : heap.Region (block store p) := by
  have := h.below
  have := h.base
  exact ⟨by simp only [block]; omega, h.separate⟩

mutual
/-- Every block of an owned value is a region of the heap. -/
theorem NodeOwned.regions {heap : Heap} {store : Store Unit} :
    ∀ (p : UInt64) (n : Node), NodeOwned heap store p n → ∀ b ∈ n.blocks store p, heap.Region b
  | _, .null, _, _, hb => nomatch hb
  | p, .record slots, ⟨hHead, hSlots⟩, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hHead.region
      · exact SlotsOwned.regions p 0 slots hSlots b hb

theorem SlotsOwned.regions {heap : Heap} {store : Store Unit} :
    ∀ (p : UInt64) (i : Nat) (slots : List Slot), SlotsOwned heap store p i slots →
      ∀ b ∈ slotsBlocks store p i slots, heap.Region b
  | _, _, [], _, _, hb => nomatch hb
  | p, i, .word _ :: rest, ⟨_, hRest⟩, b, hb => SlotsOwned.regions p (i + 1) rest hRest b hb
  | p, i, .child n :: rest, ⟨hChild, hRest⟩, b, hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact NodeOwned.regions _ n hChild b hb
      · exact SlotsOwned.regions p (i + 1) rest hRest b hb
end

/-- The value `n`, owned at `p` in `heap'` and `store`, built from `heap` and `initial`: the
allocator invariant holds, the value's blocks are pairwise disjoint, every region of `heap`
keeps its bytes, stays a region, and lies apart from the value's blocks, memory has not
shrunk, and the memory limits are unchanged. -/
structure Heap.Built (heap : Heap) (initial : Store Unit) (heap' : Heap) (store : Store Unit)
    (p : UInt64) (n : Node) : Prop where
  at_ : heap'.At store
  owned : NodeOwned heap' store p n
  disjoint : (n.blocks store p).Pairwise regionsDisjoint
  region : ∀ r, heap.Region r →
    (∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a) ∧
      heap'.Region r ∧ ∀ b ∈ n.blocks store p, regionsDisjoint r b
  pages : initial.mem.pages ≤ store.mem.pages
  caps : store.memoryCaps = initial.memoryCaps

/-- The null pointer is the empty value, built from any heap. -/
theorem Heap.Built.null {heap : Heap} {initial : Store Unit} (h : heap.At initial) :
    heap.Built initial heap initial 0 .null :=
  ⟨h, rfl, .nil, fun _ hr => ⟨fun _ _ _ => rfl, hr, fun _ hb => nomatch hb⟩, le_refl _, rfl⟩

/-- A record allocated and filled with the word `x` and the pointer `p` to a built value
`n` holds the list cell of `x` and `n`. -/
theorem Heap.Built.cell {heap heap1 heap2 : Heap} {initial store1 store2 : Store Unit}
    {p ptr x : UInt64} {n : Node} (h : heap.Built initial heap1 store1 p n)
    (hNew : heap1.NewRecord store1 heap2 store2 ptr [x, p] 2) :
    heap.Built initial heap2 store2 ptr (.record [.word x, .child n]) := by
  have hOld := NodeOwned.regions p n h.owned
  obtain ⟨hOwned, hBlocks⟩ := NodeOwned.frame p n h.owned fun b hb =>
    ⟨(hNew.region b (hOld b hb)).1, (hNew.region b (hOld b hb)).2.1⟩
  have hx : store2.mem.read64 (slotAddress ptr 0) = x := hNew.slots 0 (by simp)
  have hp : store2.mem.read64 (slotAddress ptr 1) = p := hNew.slots 1 (by simp)
  have hNewBlocks : Node.blocks store2 ptr (.record [.word x, .child n]) =
      block store2 ptr :: n.blocks store1 p := by
    simp only [Node.blocks, slotsBlocks, hp, hBlocks, List.append_nil]
  refine ⟨hNew.at_, ⟨hNew.header _ rfl rfl, hx, by rw [hp]; exact hOwned, trivial⟩, ?_,
    fun r hr => ?_, h.pages.trans hNew.pages, hNew.caps.trans h.caps⟩
  · rw [hNewBlocks]
    exact .cons (fun b hb => regionsDisjoint_symm (hNew.region b (hOld b hb)).2.2) h.disjoint
  · obtain ⟨hBytes, hRegion, hApart⟩ := h.region r hr
    obtain ⟨hBytes', hRegion', hNewApart⟩ := hNew.region r hRegion
    refine ⟨fun a hLow hHigh => (hBytes' a hLow hHigh).trans (hBytes a hLow hHigh), hRegion',
      fun b hb => ?_⟩
    rw [hNewBlocks] at hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hNewApart
    · exact hApart b hb

/-- A value built from `heap` keeps every array that `heap` lends or owns, and lies apart
from it. -/
theorem Heap.Built.keepBorrowed {heap heap' : Heap} {initial store : Store Unit} {p q : UInt64}
    {n : Node} {ws : Array UInt64} (h : heap.Built initial heap' store p n)
    (hq : heap.Borrowed initial q ws) :
    heap'.Borrowed store q ws ∧ ∀ b ∈ n.blocks store p,
      regionsDisjoint (q.toNat, 8 * (ws.size + 1)) b := by
  obtain ⟨hBytes, hRegion, hApart⟩ := h.region _ hq.region
  exact ⟨⟨arrayAt_frame hq.values h.pages hBytes, hRegion.below,
    fun node hNode => regionsDisjoint_symm (hRegion.separate node hNode)⟩, hApart⟩

theorem Heap.Built.keepOwned {heap heap' : Heap} {initial store : Store Unit} {p q : UInt64}
    {n : Node} {ws : Array UInt64} (h : heap.Built initial heap' store p n)
    (hq : heap.Owned initial q ws) :
    (heap'.Owned store q ws ∧ capacityAt store q = capacityAt initial q) ∧
      ∀ b ∈ n.blocks store p, regionsDisjoint (q.toNat - 48, 48 + capacityAt initial q) b := by
  obtain ⟨hBytes, hRegion, hApart⟩ := h.region _ hq.region
  have := hq.base
  have := hq.address
  simp only [block] at hBytes hRegion hApart
  refine ⟨⟨Heap.Owned.frame hq h.pages (fun a hLow hHigh => hBytes a hLow (by omega))
      (by have := hRegion.below; simp only at this; omega) hRegion.separate,
    capacityAt_frame (by omega) (by omega) fun a hLow hHigh => hBytes a hLow (by omega)⟩,
    hApart⟩

/-- The list of words `xs` at `p` in `mem`: the null pointer for `[]`, and for `x :: xs` a
nonzero pointer to two words inside memory and the 32-bit address space, the first `x` and
the second a pointer to `xs`. -/
def ListAt (mem : Mem) : UInt64 → List UInt64 → Prop
  | p, [] => p = 0
  | p, x :: xs => p ≠ 0 ∧ p.toNat + 16 < 4294967296 ∧ p.toNat + 16 ≤ mem.pages * 65536 ∧
      mem.read64 (slotAddress p 0) = x ∧ ListAt mem (mem.read64 (slotAddress p 1)) xs

theorem ListAt.unique {mem : Mem} : ∀ {p : UInt64} {xs ys : List UInt64},
    ListAt mem p xs → ListAt mem p ys → xs = ys
  | _, [], [], _, _ => rfl
  | _, [], _ :: _, h, ⟨h0, _⟩ => absurd h h0
  | _, _ :: _, [], ⟨h0, _⟩, h => absurd h h0
  | _, _ :: _, _ :: _, ⟨_, _, _, hx, hxs⟩, ⟨_, _, _, hy, hys⟩ => by
      rw [← hx, ← hy, ListAt.unique hxs hys]

/-- The length of the list of words at `p` in `mem`, or 0 when `p` heads none. -/
noncomputable def listLength (mem : Mem) (p : UInt64) : Nat :=
  open Classical in if h : ∃ xs, ListAt mem p xs then (Classical.choose h).length else 0

theorem ListAt.listLength {mem : Mem} {p : UInt64} {xs : List UInt64} (h : ListAt mem p xs) :
    listLength mem p = xs.length := by
  have hExists : ∃ xs, ListAt mem p xs := ⟨xs, h⟩
  simp only [Pipeline.listLength, hExists, ↓reduceDIte]
  rw [ListAt.unique (Classical.choose_spec hExists) h]

/-- A borrowed list of words heads a list in memory. -/
theorem NodeBorrowed.listAt {heap : Heap} {store : Store Unit} (hHeap : heap.At store) :
    ∀ {p : UInt64} {xs : List UInt64}, NodeBorrowed heap store p (encodeList xs) →
      ListAt store.mem p xs
  | _, [], h => h
  | _, _ :: _, ⟨hSlots, hx, hChild, _⟩ => by
      have := hSlots.address
      have := hSlots.below
      have := hHeap.top
      simp only [List.length_cons, List.length_nil] at *
      exact ⟨hSlots.nonzero, by omega, by omega, hx, NodeBorrowed.listAt hHeap hChild⟩

end Project.Pipeline
