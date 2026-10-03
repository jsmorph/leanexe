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

/-- Slot `i` of a record lies `8 * i` bytes after its pointer. -/
theorem slotAddress_toNat {p : UInt64} {i : Nat} (h : p.toNat + 8 * i < 4294967296) :
    (slotAddress p i).toNat = p.toNat + 8 * i := by
  unfold slotAddress
  rw [Memory.toUInt32_toNat, UInt64.toNat_add, UInt64.toNat_ofNat']
  omega

/-- A record keeps its header and capacity when the bytes of its header do, and it may hold
any slots of the same number and child mask; it stays owned in any heap whose free blocks and
`top` leave its block alone. -/
theorem RecordHeader.rewrite {heap heap' : Heap} {store store' : Store Unit} {p : UInt64}
    {slots slots' : List Slot} (h : RecordHeader heap store p slots)
    (hBytes : ∀ a, p.toNat - 48 ≤ a → a < p.toNat → store'.mem.bytes a = store.mem.bytes a)
    (hLength : slots'.length = slots.length) (hMask : maskOf slots' = maskOf slots)
    (hRegion : heap'.Region (block store p)) :
    RecordHeader heap' store' p slots' ∧ capacityAt store' p = capacityAt store p := by
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
  have hShort := h.short
  have hRoom := h.capacity
  simp only [block] at hBelow hSeparate
  refine ⟨⟨hBase, ?_, ?_, ?_, ?_, ?_, by omega, ?_, ?_, ?_, ?_⟩, hCapacity⟩
  · rw [hHeader 48 (by decide) (by decide)]; exact h.magic
  · rw [hHeader 40 (by decide) (by decide)]; exact h.count
  · rw [hHeader 24 (by decide) (by decide)]; exact h.kind
  · rw [hHeader 16 (by decide) (by decide), hLength]; exact h.width
  · rw [hHeader 8 (by decide) (by decide), hMask]; exact h.mask
  · rw [hCapacity]; omega
  · rw [hCapacity]; exact hAddress
  · rw [hCapacity]; omega
  · rw [hCapacity]; exact hSeparate

/-- A record keeps its header and capacity when the bytes of its block do, and it stays
owned in any heap whose free blocks and `top` leave its block alone. -/
theorem RecordHeader.frame {heap heap' : Heap} {store store' : Store Unit} {p : UInt64}
    {slots : List Slot} (h : RecordHeader heap store p slots)
    (hBytes : ∀ a, p.toNat - 48 ≤ a → a < p.toNat + capacityAt store p →
      store'.mem.bytes a = store.mem.bytes a)
    (hRegion : heap'.Region (block store p)) :
    RecordHeader heap' store' p slots ∧ capacityAt store' p = capacityAt store p :=
  h.rewrite (fun a hLow hHigh => hBytes a hLow (by omega)) rfl rfl hRegion

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
      (∀ a, p.toNat + 8 * i ≤ a → a < p.toNat + 8 * (i + slots.length) →
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
        (fun a hLow hHigh => hBytes a (by omega) (by omega)) hBlocks
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
        (fun a hLow hHigh => hBytes a (by omega) (by omega)) (fun b hb => hBlocks b (.inr hb))
      refine ⟨⟨by rw [hRead]; exact hChild', hRest'⟩, ?_⟩
      simp only [slotsBlocks, hRead, hChildBlocks, hRestBlocks]
end

mutual
/-- A borrowed value keeps its records when the bytes of its slot regions are unchanged and
every slot region is a region of the new heap. -/
theorem NodeBorrowed.frame {heap heap' : Heap} {store store' : Store Unit} :
    ∀ (p : UInt64) (n : Node), NodeBorrowed heap store p n →
      (∀ b ∈ n.slotRegions store p, (∀ a, b.1 ≤ a → a < b.1 + b.2 →
        store'.mem.bytes a = store.mem.bytes a) ∧ heap'.Region b) →
      NodeBorrowed heap' store' p n ∧ n.slotRegions store' p = n.slotRegions store p
  | _, .null, h, _ => ⟨h, rfl⟩
  | p, .record slots, ⟨hRec, hSlots⟩, hR => by
      have hFirst := hR (p.toNat, 8 * slots.length) List.mem_cons_self
      have hAddress := hRec.address
      obtain ⟨hSlots', hRest⟩ := SlotsBorrowed.frame p 0 slots hSlots (by omega)
        (fun a hLow hHigh => hFirst.1 a (by simp only; omega) (by simp only; omega))
        (fun b hb => hR b (List.mem_cons_of_mem _ hb))
      exact ⟨⟨⟨hRec.nonzero, hRec.address, hFirst.2.below,
          fun node hNode => regionsDisjoint_symm (hFirst.2.separate node hNode)⟩, hSlots'⟩,
        by simp only [Node.slotRegions, hRest]⟩

theorem SlotsBorrowed.frame {heap heap' : Heap} {store store' : Store Unit} :
    ∀ (p : UInt64) (i : Nat) (slots : List Slot), SlotsBorrowed heap store p i slots →
      p.toNat + 8 * (i + slots.length) < 4294967296 →
      (∀ a, p.toNat + 8 * i ≤ a → a < p.toNat + 8 * (i + slots.length) →
        store'.mem.bytes a = store.mem.bytes a) →
      (∀ b ∈ slotsRegions store p i slots, (∀ a, b.1 ≤ a → a < b.1 + b.2 →
        store'.mem.bytes a = store.mem.bytes a) ∧ heap'.Region b) →
      SlotsBorrowed heap' store' p i slots ∧
        slotsRegions store' p i slots = slotsRegions store p i slots
  | _, _, [], _, _, _, _ => ⟨trivial, rfl⟩
  | p, i, .word w :: rest, ⟨hWord, hRest⟩, hAddress, hBytes, hR => by
      simp only [List.length_cons] at hAddress hBytes
      have hRead : store'.mem.read64 (slotAddress p i) = store.mem.read64 (slotAddress p i) :=
        Memory.read64_congr _ fun k hk => by
          rw [slotAddress_toNat (by omega)]
          exact hBytes _ (by omega) (by omega)
      obtain ⟨hRest', hR'⟩ := SlotsBorrowed.frame p (i + 1) rest hRest (by omega)
        (fun a hLow hHigh => hBytes a (by omega) (by omega)) hR
      exact ⟨⟨hRead.trans hWord, hRest'⟩, hR'⟩
  | p, i, .child n :: rest, ⟨hChild, hRest⟩, hAddress, hBytes, hR => by
      simp only [List.length_cons] at hAddress hBytes
      have hRead : store'.mem.read64 (slotAddress p i) = store.mem.read64 (slotAddress p i) :=
        Memory.read64_congr _ fun k hk => by
          rw [slotAddress_toNat (by omega)]
          exact hBytes _ (by omega) (by omega)
      simp only [slotsRegions, List.mem_append] at hR
      obtain ⟨hChild', hChildR⟩ := NodeBorrowed.frame _ n hChild (fun b hb => hR b (.inl hb))
      obtain ⟨hRest', hRestR⟩ := SlotsBorrowed.frame p (i + 1) rest hRest (by omega)
        (fun a hLow hHigh => hBytes a (by omega) (by omega)) (fun b hb => hR b (.inr hb))
      refine ⟨⟨by rw [hRead]; exact hChild', hRest'⟩, ?_⟩
      simp only [slotsRegions, hRead, hChildR, hRestR]
end

mutual
/-- Every slot region of a borrowed value is a region of the heap. -/
theorem NodeBorrowed.regions {heap : Heap} {store : Store Unit} :
    ∀ (p : UInt64) (n : Node), NodeBorrowed heap store p n →
      ∀ b ∈ n.slotRegions store p, heap.Region b
  | _, .null, _, _, hb => nomatch hb
  | p, .record slots, ⟨hRec, hSlots⟩, b, hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨hRec.below, fun node hNode => regionsDisjoint_symm (hRec.separate node hNode)⟩
      · exact SlotsBorrowed.regions p 0 slots hSlots b hb

theorem SlotsBorrowed.regions {heap : Heap} {store : Store Unit} :
    ∀ (p : UInt64) (i : Nat) (slots : List Slot), SlotsBorrowed heap store p i slots →
      ∀ b ∈ slotsRegions store p i slots, heap.Region b
  | _, _, [], _, _, hb => nomatch hb
  | p, i, .word _ :: rest, ⟨_, hRest⟩, b, hb => SlotsBorrowed.regions p (i + 1) rest hRest b hb
  | p, i, .child n :: rest, ⟨hChild, hRest⟩, b, hb => by
      rcases List.mem_append.mp hb with hb | hb
      · exact NodeBorrowed.regions _ n hChild b hb
      · exact SlotsBorrowed.regions p (i + 1) rest hRest b hb
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
  caps : store.memoryCaps = initial.memoryCaps

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
keeps its bytes, stays a region, and lies apart from the value's blocks, and the memory
limits are unchanged. -/
structure Heap.Built (heap : Heap) (initial : Store Unit) (heap' : Heap) (store : Store Unit)
    (p : UInt64) (n : Node) : Prop where
  at_ : heap'.At store
  owned : NodeOwned heap' store p n
  disjoint : (n.blocks store p).Pairwise regionsDisjoint
  region : ∀ r, heap.Region r →
    (∀ a, r.1 ≤ a → a < r.1 + r.2 → store.mem.bytes a = initial.mem.bytes a) ∧
      heap'.Region r ∧ ∀ b ∈ n.blocks store p, regionsDisjoint r b
  caps : store.memoryCaps = initial.memoryCaps

/-- The null pointer is the empty value, built from any heap. -/
theorem Heap.Built.null {heap : Heap} {initial : Store Unit} (h : heap.At initial) :
    heap.Built initial heap initial 0 .null :=
  ⟨h, rfl, .nil, fun _ hr => ⟨fun _ _ _ => rfl, hr, fun _ hb => nomatch hb⟩, rfl⟩

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
    fun r hr => ?_, hNew.caps.trans h.caps⟩
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

theorem maskOf_cons (s : Slot) (rest : List Slot) :
    maskOf (s :: rest) = 2 * maskOf rest + s.bit := rfl

theorem Slot.bit_le (s : Slot) : s.bit.toNat ≤ 1 := by cases s <;> simp [Slot.bit]

/-- The mask of at most 64 slots is below `2 ^ length`, and its bit `i` is slot `i`'s bit. -/
theorem maskOf_toNat : ∀ (slots : List Slot), slots.length ≤ 64 →
    (maskOf slots).toNat < 2 ^ slots.length ∧
    ∀ i (h : i < slots.length), (maskOf slots).toNat / 2 ^ i % 2 = (slots[i].bit).toNat
  | [], _ => ⟨by decide, fun i h => absurd h (by simp)⟩
  | s :: rest, hLen => by
      simp only [List.length_cons] at hLen
      obtain ⟨hLt, hBits⟩ := maskOf_toNat rest (by omega)
      have hb := Slot.bit_le s
      have hPow : 2 ^ rest.length ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
      have hEq : (maskOf (s :: rest)).toNat = 2 * (maskOf rest).toNat + s.bit.toNat := by
        rw [maskOf_cons, UInt64.toNat_add, UInt64.toNat_mul]
        have : (2 : UInt64).toNat = 2 := rfl
        rw [this, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      refine ⟨by rw [hEq, List.length_cons, Nat.pow_succ]; omega, fun i h => ?_⟩
      rw [hEq]
      cases i with
      | zero => simp; omega
      | succ j =>
        simp only [List.getElem_cons_succ]
        rw [← hBits j (by simp at h; omega), Nat.pow_succ', ← Nat.div_div_eq_div_mul]
        congr 2
        omega

/-- The runtime's mask test for slot `i`, a shift by `i` modulo 64 and a mask of the low
bit, reads the slot's bit. -/
theorem maskOf_test (slots : List Slot) (hLen : slots.length ≤ 64) (i : Nat)
    (h : i < slots.length) :
    ((maskOf slots >>> (UInt64.ofNat i % 64)) &&& 1) = slots[i].bit := by
  obtain ⟨-, hBits⟩ := maskOf_toNat slots hLen
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  have hi : (UInt64.ofNat i % 64).toNat % 64 = i := by
    rw [UInt64.toNat_mod, UInt64.toNat_ofNat']
    have : (64 : UInt64).toNat = 64 := rfl
    rw [this]
    omega
  rw [hi, Nat.shiftRight_eq_div_pow]
  have : (1 : UInt64).toNat = 1 := rfl
  rw [this, Nat.and_one_is_mod, hBits i h]

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

/-- An owned list of words heads a list in memory. -/
theorem NodeOwned.listAt {heap : Heap} {store : Store Unit} (hHeap : heap.At store) :
    ∀ {p : UInt64} {xs : List UInt64}, NodeOwned heap store p (encodeList xs) →
      ListAt store.mem p xs
  | _, [], h => h
  | _, _ :: _, ⟨hHead, hx, hChild, _⟩ => by
      have hBase := hHead.base
      have := hHead.address
      have := hHead.below
      have := hHead.capacity
      have := hHeap.top
      simp only [List.length_cons, List.length_nil] at *
      exact ⟨fun h => by rw [h] at hBase; simp at hBase, by omega, by omega, hx,
        NodeOwned.listAt hHeap hChild⟩

/-- Replacing a word slot by a word keeps the child mask. -/
theorem maskOf_set_word : ∀ (slots : List Slot) (i : Nat) (v w : UInt64),
    slots[i]? = some (.word v) → maskOf (slots.set i (.word w)) = maskOf slots
  | [], _, _, _, h => nomatch h
  | _ :: _, 0, _, _, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rfl
  | _ :: rest, i + 1, v, w, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.set_cons_succ, maskOf_cons, maskOf_set_word rest i v w h]

/-- Slots `j` on of an owned record with a word in slot `i` hold `w` there and keep their other
slots and blocks in a store that holds `w` in slot `i` and keeps every other byte of the slots
and every byte of the children's blocks. -/
theorem SlotsOwned.writeWord {heap : Heap} {store store' : Store Unit} {p w : UInt64} {i : Nat}
    (hWritten : store'.mem.read64 (slotAddress p i) = w) :
    ∀ (j : Nat) (slots : List Slot), SlotsOwned heap store p j slots → j ≤ i →
      (∃ v, slots[i - j]? = some (.word v)) →
      p.toNat + 8 * (j + slots.length) < 4294967296 →
      (∀ a, p.toNat + 8 * j ≤ a → a < p.toNat + 8 * (j + slots.length) →
        a < p.toNat + 8 * i ∨ p.toNat + 8 * i + 8 ≤ a → store'.mem.bytes a = store.mem.bytes a) →
      (∀ b ∈ slotsBlocks store p j slots, ∀ a, b.1 ≤ a → a < b.1 + b.2 →
        store'.mem.bytes a = store.mem.bytes a) →
      SlotsOwned heap store' p j (slots.set (i - j) (.word w)) ∧
        slotsBlocks store' p j (slots.set (i - j) (.word w)) = slotsBlocks store p j slots
  | _, [], _, _, ⟨_, hv⟩, _, _, _ => by simp at hv
  | j, .word u :: rest, ⟨hWord, hRest⟩, hj, ⟨v, hv⟩, hAddress, hBytes, hBlocks => by
      simp only [List.length_cons] at hAddress hBytes
      by_cases hij : i = j
      · subst hij
        rw [Nat.sub_self, List.set_cons_zero]
        have hRegions := SlotsOwned.regions p (i + 1) rest hRest
        obtain ⟨hRest', hBlocks'⟩ := SlotsOwned.frame p (i + 1) rest hRest (by omega)
          (fun a hLow hHigh => hBytes a (by omega) (by omega) (by omega))
          (fun b hb => ⟨hBlocks b hb, hRegions b hb⟩)
        exact ⟨⟨hWritten, hRest'⟩, hBlocks'⟩
      · have hk : i - j = (i - (j + 1)) + 1 := by omega
        rw [hk, List.set_cons_succ]
        rw [hk, List.getElem?_cons_succ] at hv
        have hRead : store'.mem.read64 (slotAddress p j) = store.mem.read64 (slotAddress p j) :=
          Memory.read64_congr _ fun k hk => by
            rw [slotAddress_toNat (by omega)]
            exact hBytes _ (by omega) (by omega) (by omega)
        obtain ⟨hRest', hBlocks'⟩ := SlotsOwned.writeWord hWritten (j + 1) rest hRest (by omega)
          ⟨v, hv⟩ (by omega) (fun a hLow hHigh hOut => hBytes a (by omega) (by omega) hOut) hBlocks
        exact ⟨⟨hRead.trans hWord, hRest'⟩, hBlocks'⟩
  | j, .child n :: rest, ⟨hChild, hRest⟩, hj, ⟨v, hv⟩, hAddress, hBytes, hBlocks => by
      simp only [List.length_cons] at hAddress hBytes
      have hij : i ≠ j := by
        rintro rfl
        simp at hv
      have hk : i - j = (i - (j + 1)) + 1 := by omega
      rw [hk, List.set_cons_succ]
      rw [hk, List.getElem?_cons_succ] at hv
      have hRead : store'.mem.read64 (slotAddress p j) = store.mem.read64 (slotAddress p j) :=
        Memory.read64_congr _ fun k hk => by
          rw [slotAddress_toNat (by omega)]
          exact hBytes _ (by omega) (by omega) (by omega)
      simp only [slotsBlocks, List.mem_append] at hBlocks
      obtain ⟨hChild', hChildBlocks⟩ := NodeOwned.frame _ n hChild fun b hb =>
        ⟨hBlocks b (.inl hb), NodeOwned.regions _ n hChild b hb⟩
      obtain ⟨hRest', hRestBlocks⟩ := SlotsOwned.writeWord hWritten (j + 1) rest hRest (by omega)
        ⟨v, hv⟩ (by omega) (fun a hLow hHigh hOut => hBytes a (by omega) (by omega) hOut)
        (fun b hb => hBlocks b (.inr hb))
      refine ⟨⟨by rw [hRead]; exact hChild', hRest'⟩, ?_⟩
      simp only [slotsBlocks, hRead, hChildBlocks, hRestBlocks]

/-- Writing the word `w` into slot `i` of an owned record that holds a word there, whose blocks
are pairwise disjoint, changes only the slot's bytes, keeps the allocator invariant, and gives
the record with `w` in slot `i` and the same blocks. -/
theorem NodeOwned.writeWord {heap : Heap} {store : Store Unit} {p w : UInt64}
    {slots : List Slot} {i : Nat} (hHeap : heap.At store)
    (h : NodeOwned heap store p (.record slots))
    (hDisjoint : (Node.blocks store p (.record slots)).Pairwise regionsDisjoint)
    (hWord : ∃ v, slots[i]? = some (.word v)) :
    Memory.WritesRange store { store with mem := store.mem.write64 (slotAddress p i) w }
        (p.toNat + 8 * i) (p.toNat + 8 * i + 8) ∧
      heap.At { store with mem := store.mem.write64 (slotAddress p i) w } ∧
      NodeOwned heap { store with mem := store.mem.write64 (slotAddress p i) w } p
        (.record (slots.set i (.word w))) ∧
      Node.blocks { store with mem := store.mem.write64 (slotAddress p i) w } p
        (.record (slots.set i (.word w))) = Node.blocks store p (.record slots) := by
  obtain ⟨hHead, hSlots⟩ := h
  obtain ⟨v, hv⟩ := hWord
  have hi : i < slots.length := (List.getElem?_eq_some_iff.mp hv).1
  have hRoom := hHead.capacity
  have hAddress := hHead.address
  have hBase := hHead.base
  have hSlot := slotAddress_toNat (p := p) (i := i) (by omega)
  have hWrites := Memory.WritesRange.write64 store (slotAddress p i) w (p.toNat + 8 * i)
    (p.toNat + 8 * i + 8) (by omega) (by omega)
  obtain ⟨hHead', hCapacity⟩ := hHead.rewrite
    (store' := { store with mem := store.mem.write64 (slotAddress p i) w })
    (fun a hLow hHigh => hWrites.2.2 a (.inl (by omega))) List.length_set
    (maskOf_set_word slots i v w hv) hHead.region
  have hApart := (List.pairwise_cons.mp hDisjoint).1
  obtain ⟨hSlots', hBlocks⟩ := SlotsOwned.writeWord
    (store' := { store with mem := store.mem.write64 (slotAddress p i) w })
    (Memory.read64_write64 store.mem (slotAddress p i) w) 0 slots hSlots
    (Nat.zero_le _) ⟨v, by rw [Nat.sub_zero]; exact hv⟩ (by omega)
    (fun a _ _ hOut => hWrites.2.2 a (by omega))
    (fun b hb a hLow hHigh => hWrites.2.2 a (by
      have := hApart b hb
      simp only [regionsDisjoint, block] at this
      omega))
  rw [Nat.sub_zero] at hSlots' hBlocks
  refine ⟨hWrites, hHeap.writesApart hWrites fun node hNode => ?_, ⟨hHead', hSlots'⟩, ?_⟩
  · have := hHead.separate node hNode
    simp only [regionsDisjoint] at this ⊢
    omega
  · simp only [Node.blocks, block_eq hCapacity, hBlocks]

mutual
/-- The blocks of a value's records are the blocks at its record pointers. -/
theorem Node.pointers_blocks (store : Store Unit) : ∀ (p : UInt64) (n : Node),
    (Node.pointers store p n).map (block store) = Node.blocks store p n
  | _, .null => rfl
  | p, .record slots => by
      simp only [Node.pointers, Node.blocks, List.map_cons, slotsPointers_blocks store p 0 slots]

theorem slotsPointers_blocks (store : Store Unit) : ∀ (p : UInt64) (i : Nat) (slots : List Slot),
    (slotsPointers store p i slots).map (block store) = slotsBlocks store p i slots
  | _, _, [] => rfl
  | p, i, .word _ :: rest => by
      simp only [slotsPointers, slotsBlocks, slotsPointers_blocks store p (i + 1) rest]
  | p, i, .child n :: rest => by
      simp only [slotsPointers, slotsBlocks, List.map_append, Node.pointers_blocks store _ n,
        slotsPointers_blocks store p (i + 1) rest]
end

/-- A region lies apart from the records of a value exactly when it lies apart from each of
the value's blocks. -/
theorem apart_pointers {store : Store Unit} {p : UInt64} {n : Node} {r : Nat × Nat} :
    Apart store (Node.pointers store p n) r ↔ ∀ b ∈ Node.blocks store p n, regionsDisjoint r b := by
  rw [← Node.pointers_blocks]
  simp [Apart]

end Project.Pipeline
