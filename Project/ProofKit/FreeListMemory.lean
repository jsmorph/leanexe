import Project.Runtime.FreeList
import Project.ProofKit.FixedArrayHeader

namespace Project.ProofKit

open Wasm Project.Common Project.Runtime

def fixedArrayAllocFitMem (mem : Mem) (choice : FreeChoice)
    (stride : UInt64) : Mem :=
  ((((((unlinkFreeChoice mem choice).write64
      ((choice.node.root - 48).toUInt32) 5501223100278326855).write64
      ((choice.node.root - 40).toUInt32) 1).write64
      ((choice.node.root - 32).toUInt32) choice.node.capacity).write64
      ((choice.node.root - 24).toUInt32) 2).write64
      ((choice.node.root - 16).toUInt32) stride).write64
      ((choice.node.root - 8).toUInt32) 0

def fixedArrayAllocFitStore (st : Store Unit) (choice : FreeChoice)
    (stride : UInt64) : Store Unit :=
  { st with
    globals := if choice.previous = 0 then
      { globals := st.globals.globals.set 1 (.i64 choice.next) }
    else
      st.globals
    mem := fixedArrayAllocFitMem st.mem choice stride }

theorem freeListAt_fixedArrayAllocFitMem
    {mem : Mem} {nodes : List FreeNode}
    {need : UInt64} {choice : FreeChoice}
    (stride : UInt64)
    (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    FreeListAt (fixedArrayAllocFitMem mem choice stride)
      choice.remaining := by
  have hChoiceMem : choice.node ∈ nodes :=
    takeFirstFitFrom_some_mem hTake
  obtain ⟨hNode48, hNode32, _⟩ := hList.mem_bounds hChoiceMem
  have hsep := hList.takeFirstFitFrom_node_disjoint hTake
  have h0 := hList.unlink_takeFirstFitFrom hTake
  have h1 := h0.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 48)
    (value := 5501223100278326855) hNode48 hNode32
    (by decide) (by decide) hsep
  have h2 := h1.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 40) (value := 1)
    hNode48 hNode32 (by decide) (by decide) hsep
  have h3 := h2.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 32)
    (value := choice.node.capacity) hNode48 hNode32
    (by decide) (by decide) hsep
  have h4 := h3.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 24) (value := 2)
    hNode48 hNode32 (by decide) (by decide) hsep
  have h5 := h4.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 16) (value := stride)
    hNode48 hNode32 (by decide) (by decide) hsep
  have h6 := h5.frame_write64_disjoint
    (writer := choice.node) (writeOffset := 8) (value := 0)
    hNode48 hNode32 (by decide) (by decide) hsep
  exact h6

theorem freshFixedArrayAt_fixedArrayAllocFitStore
    {st : Store Unit} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} (stride : UInt64)
    (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    FreshFixedArrayAt (fixedArrayAllocFitStore st choice stride)
      choice.node.root choice.node.capacity stride := by
  have hChoiceMem : choice.node ∈ nodes :=
    takeFirstFitFrom_some_mem hTake
  obtain ⟨hRoot48, hRoot32, _⟩ := hList.mem_bounds hChoiceMem
  have hBase : (choice.node.root - 48).toNat + 48 ≤ 4294967296 := by
    rw [Project.ProofKit.Memory.toNat_sub_of_le choice.node.root 48 hRoot48]
    change choice.node.root.toNat - 48 + 48 ≤ 4294967296
    omega
  let unlinked : Store Unit := { st with mem := unlinkFreeChoice st.mem choice }
  have hFresh := Project.ProofKit.FixedArrayHeader.fresh unlinked
    (choice.node.root - 48) choice.node.capacity stride hBase
  rw [Project.ProofKit.FixedArrayHeader.from_root _ _ _ _ hRoot48 (by omega)] at hFresh
  simpa only [FreshFixedArrayAt, UInt64.sub_add_cancel, unlinked,
    fixedArrayAllocFitStore, fixedArrayAllocFitMem] using hFresh

end Project.ProofKit

namespace Project.ProofKit.FreeListMemory
open Wasm Project.Runtime Project.ProofKit.Memory

theorem previous_mem {need : UInt64} {nodes : List FreeNode} {choice : FreeChoice}
    (hTake : takeFirstFitFrom 0 need nodes = some choice) (hNonzero : choice.previous ≠ 0) :
    ∃ node ∈ nodes, choice.previous = node.root := by
  obtain ⟨skipped, tail, hNodes, hPrevious, _, _, _⟩ :=
    takeFirstFitFrom_some_decompose hTake
  have hSkipped : skipped ≠ [] := by
    intro hEmpty
    exact hNonzero (by simpa [hEmpty, previousRoot] using hPrevious)
  let predecessor := skipped.getLast hSkipped
  have hSplit : skipped.dropLast ++ [predecessor] = skipped :=
    List.dropLast_append_getLast hSkipped
  refine ⟨predecessor, ?_, ?_⟩
  · rw [hNodes, ← hSplit]
    simp
  · rw [hPrevious, ← hSplit, previousRoot_append_singleton]

theorem frame_grow {mem mem' : Mem} {nodes : List FreeNode} (hList : FreeListAt mem nodes)
    (hPages : mem.pages ≤ mem'.pages) (hBytes : mem'.bytes = mem.bytes) :
    FreeListAt mem' nodes := by
  have hRead (address : UInt32) : mem'.read64 address = mem.read64 address := by
    exact read64_congr address (by intro i hi; rw [hBytes])
  induction hList with
  | nil => exact .nil
  | cons h48 h32 hFit hRc hCapacity hNext hSep hTail ih =>
    exact .cons h48 h32 (hFit.trans (Nat.mul_le_mul_right 65536 hPages))
      ((hRead _).trans hRc) ((hRead _).trans hCapacity) ((hRead _).trans hNext) hSep ih

theorem fit_bytes {mem : Mem} {nodes : List FreeNode} {need : UInt64} {choice : FreeChoice}
    (stride : UInt64) (lower upper address : Nat) (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSep : ∀ node ∈ nodes, upper ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ lower)
    (hLow : lower ≤ address) (hHigh : address < upper) :
    (fixedArrayAllocFitMem mem choice stride).bytes address = mem.bytes address := by
  have frameWrite (current : Mem) (writer : FreeNode) (hWriter : writer ∈ nodes)
      (offset value : UInt64) (hOffsetLow : 8 ≤ offset.toNat) (hOffsetHigh : offset.toNat ≤ 48) :
      (current.write64 (writer.root - offset).toUInt32 value).bytes address =
        current.bytes address := by
    obtain ⟨h48, h32, _⟩ := hList.mem_bounds hWriter
    have hDisjoint := hSep writer hWriter
    apply write64_bytes_outside
    rw [UInt64.toNat_toUInt32, toNat_sub_of_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
    omega
  have hChoiceMem := takeFirstFitFrom_some_mem hTake
  have hUnlink : (unlinkFreeChoice mem choice).bytes address = mem.bytes address := by
    by_cases hPrevious : choice.previous = 0
    · simp [unlinkFreeChoice, hPrevious]
    · obtain ⟨predecessor, hPredecessor, hRoot⟩ := previous_mem hTake hPrevious
      rw [unlinkFreeChoice, ite_eq_right hPrevious, hRoot]
      exact frameWrite mem predecessor hPredecessor 8 choice.next (by decide) (by decide)
  unfold fixedArrayAllocFitMem
  rw [frameWrite _ choice.node hChoiceMem 8 0 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 16 stride (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 24 2 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 32 choice.node.capacity (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 40 1 (by decide) (by decide),
    frameWrite _ choice.node hChoiceMem 48 5501223100278326855 (by decide) (by decide), hUnlink]

theorem frame_headers {mem mem' : Mem} {nodes : List FreeNode}
    (hList : FreeListAt mem nodes) (hPages : mem.pages ≤ mem'.pages)
    (hBytes : ∀ node ∈ nodes, ∀ address : Nat,
      node.root.toNat - 48 ≤ address → address < node.root.toNat →
      mem'.bytes address = mem.bytes address) : FreeListAt mem' nodes := by
  revert hBytes
  induction hList with
  | nil => exact fun _ => .nil
  | @cons node rest h48 h32 hFit hRc hCapacity hNext hSep hTail ih =>
    intro hBytes
    have hRead (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
        mem'.read64 (node.root - offset).toUInt32 = mem.read64 (node.root - offset).toUInt32 := by
      apply read64_congr
      intro i hi
      rw [UInt64.toNat_toUInt32, toNat_sub_of_le _ _ (by omega), Nat.mod_eq_of_lt (by omega)]
      exact hBytes node List.mem_cons_self _ (by omega) (by omega)
    exact .cons h48 h32 (hFit.trans (Nat.mul_le_mul_right 65536 hPages))
      ((hRead 40 (by decide) (by decide)).trans hRc)
      ((hRead 32 (by decide) (by decide)).trans hCapacity)
      ((hRead 8 (by decide) (by decide)).trans hNext) hSep
      (ih (fun node hNode => hBytes node (List.mem_cons_of_mem _ hNode)))

#print axioms previous_mem
#print axioms frame_grow
#print axioms fit_bytes
#print axioms frame_headers

theorem remaining_head {mem : Mem} {nodes : List FreeNode} {need : UInt64} {choice : FreeChoice}
    (hList : FreeListAt mem nodes) (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    freeHead choice.remaining = if choice.previous = 0 then choice.next else freeHead nodes := by
  obtain ⟨skipped, tail, hNodes, hPrevious, hNext, hRemaining, _⟩ :=
    takeFirstFitFrom_some_decompose hTake
  by_cases hEmpty : skipped = []
  · simp only [hEmpty, previousRoot] at hPrevious
    simp [hRemaining, hEmpty, hPrevious, hNext]
  · let predecessor := skipped.getLast hEmpty
    have hSplit : skipped.dropLast ++ [predecessor] = skipped :=
      List.dropLast_append_getLast hEmpty
    have hRoot : choice.previous = predecessor.root := by
      rw [hPrevious, ← hSplit, previousRoot_append_singleton]
    have hMember : predecessor ∈ nodes := by
      rw [hNodes, ← hSplit]
      simp
    have hNonzero : choice.previous ≠ 0 := by
      rw [hRoot]
      exact hList.roots_ne_zero predecessor hMember
    rw [ite_eq_right hNonzero, hRemaining, hNodes]
    cases skipped with
    | nil => exact False.elim (hEmpty rfl)
    | cons first rest => rfl

#print axioms remaining_head

end Project.ProofKit.FreeListMemory

namespace Project.ProofKit

open Wasm Project.Common Project.Runtime

/-- Whether reusing `choice`'s block for `need` bytes leaves at least 56 bytes,
one header and one word, to keep as a smaller free block. -/
def splitsFit (need : UInt64) (choice : FreeChoice) : Bool :=
  56 ≤ choice.node.capacity - need

/-- The header address of the object that a split places at the upper end of
`choice`'s block. -/
def splitBase (need : UInt64) (choice : FreeChoice) : UInt64 :=
  choice.node.root + choice.node.capacity - need - 48

/-- Memory after a split: the block's size word lowered, and a fresh header at
`splitBase`. -/
def fixedArraySplitMem (mem : Mem) (choice : FreeChoice) (need stride : UInt64) : Mem :=
  fixedArrayHeaderMem
    (mem.write64 (choice.node.root - 32).toUInt32 (choice.node.capacity - need - 48))
    (splitBase need choice) need stride

/-- The store after reusing `choice`'s block for `need` bytes. -/
def fixedArrayReuseStore (st : Store Unit) (choice : FreeChoice) (need stride : UInt64) :
    Store Unit :=
  if splitsFit need choice then { st with mem := fixedArraySplitMem st.mem choice need stride }
  else fixedArrayAllocFitStore st choice stride

/-- The payload pointer of the object made from `choice`'s block. -/
def reuseRoot (choice : FreeChoice) (need : UInt64) : UInt64 :=
  if splitsFit need choice then choice.node.root + choice.node.capacity - need
  else choice.node.root

/-- The facts about a split block in natural numbers. -/
theorem split_facts {mem : Mem} {nodes : List FreeNode} {need : UInt64} {choice : FreeChoice}
    (hList : FreeListAt mem nodes) (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSplit : splitsFit need choice = true) :
    need.toNat + 56 ≤ choice.node.capacity.toNat ∧
      (choice.node.capacity - need - 48).toNat = choice.node.capacity.toNat - need.toNat - 48 ∧
      (splitBase need choice).toNat =
        choice.node.root.toNat + choice.node.capacity.toNat - need.toNat - 48 ∧
      splitBase need choice + 48 = choice.node.root + choice.node.capacity - need ∧
      48 ≤ choice.node.root.toNat ∧
      choice.node.root.toNat + choice.node.capacity.toNat < 4294967296 ∧
      choice.node.root.toNat + choice.node.capacity.toNat ≤ mem.pages * 65536 := by
  obtain ⟨h48, h32, hFit⟩ := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
  have hNeed := UInt64.le_iff_toNat_le.mp (takeFirstFitFrom_some_capacity hTake)
  simp only [splitsFit, decide_eq_true_eq, UInt64.le_iff_toNat_le] at hSplit
  rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hNeed)] at hSplit
  simp only [UInt64.reduceToNat] at hSplit
  have hSub : (choice.node.capacity - need).toNat = choice.node.capacity.toNat - need.toNat :=
    UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hNeed)
  have hLow : (choice.node.capacity - need - 48).toNat =
      choice.node.capacity.toNat - need.toNat - 48 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hSub]; simp; omega), hSub]
    rfl
  have hSum : (choice.node.root + choice.node.capacity).toNat =
      choice.node.root.toNat + choice.node.capacity.toNat := by
    rw [UInt64.toNat_add]
    omega
  have hTop : (choice.node.root + choice.node.capacity - need).toNat =
      choice.node.root.toNat + choice.node.capacity.toNat - need.toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hSum]; omega), hSum]
  refine ⟨by omega, hLow, ?_, UInt64.sub_add_cancel _ _, h48, h32, hFit⟩
  unfold splitBase
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hTop]; simp; omega), hTop]
  rfl

theorem freeListAt_fixedArraySplitMem {mem : Mem} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} (stride : UInt64) (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSplit : splitsFit need choice = true) :
    FreeListAt (fixedArraySplitMem mem choice need stride) (shrinkFirstFit need nodes) := by
  obtain ⟨hFits, hLow, hBase, _, h48, h32, _⟩ := split_facts hList hTake hSplit
  obtain ⟨skipped, tail, hNodes, hShrink⟩ := shrinkFirstFit_decompose hTake
  rw [hNodes] at hList
  have hShrunk := hList.shrink (capacity := choice.node.capacity - need - 48) (by omega)
  rw [hShrink]
  apply FreeListMemory.frame_headers hShrunk (by simp [fixedArraySplitMem,
    fixedArrayHeaderMem])
  intro node hNode address hLowAddress hHigh
  apply FixedArrayHeader.bytes_outside _ _ _ _ (by omega)
  have hPair := hList.pairwise
  rw [List.pairwise_append] at hPair
  obtain ⟨_, hTailPair, hCross⟩ := hPair
  rcases List.mem_append.mp hNode with hSkipped | hRest
  · have := hCross node hSkipped choice.node List.mem_cons_self
    obtain ⟨hN48, _, _⟩ := hList.mem_bounds (List.mem_append_left _ hSkipped)
    simp only [regionsDisjoint, FreeNode.region] at this
    omega
  · rcases List.mem_cons.mp hRest with rfl | hTail
    · simp only at hLowAddress hHigh
      omega
    · have := List.rel_of_pairwise_cons hTailPair hTail
      obtain ⟨hN48, _, _⟩ := hList.mem_bounds
        (List.mem_append_right _ (List.mem_cons_of_mem _ hTail))
      simp only [regionsDisjoint, FreeNode.region] at this
      omega

theorem freshFixedArrayAt_fixedArraySplitMem {st : Store Unit} {nodes : List FreeNode}
    {need : UInt64} {choice : FreeChoice} (stride : UInt64) (hList : FreeListAt st.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSplit : splitsFit need choice = true) :
    FreshFixedArrayAt { st with mem := fixedArraySplitMem st.mem choice need stride }
      (choice.node.root + choice.node.capacity - need) need stride := by
  obtain ⟨_, _, hBase, hRoot, _, _, _⟩ := split_facts hList hTake hSplit
  rw [← hRoot]
  exact FixedArrayHeader.fresh
    { st with
      mem := (st.mem.write64 (choice.node.root - 32).toUInt32 (choice.node.capacity - need - 48)) }
    (splitBase need choice) need stride (by omega)

/-- A split changes no byte outside the block it splits. -/
theorem split_bytes {mem : Mem} {nodes : List FreeNode} {need : UInt64} {choice : FreeChoice}
    (stride : UInt64) (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) (hSplit : splitsFit need choice = true)
    (address : Nat) (hOutside : address < choice.node.root.toNat - 48 ∨
      choice.node.root.toNat + choice.node.capacity.toNat ≤ address) :
    (fixedArraySplitMem mem choice need stride).bytes address = mem.bytes address := by
  obtain ⟨_, _, hBase, _, h48, h32, _⟩ := split_facts hList hTake hSplit
  unfold fixedArraySplitMem
  rw [FixedArrayHeader.bytes_outside _ _ _ _ (by omega) _ (by omega),
    Project.ProofKit.Memory.write64_bytes_outside _ _ _ (by
      rw [toUInt32_toNat, toNat_sub_le _ _ (by simp; omega), Nat.mod_eq_of_lt (by simp; omega)]
      simp only [UInt64.reduceToNat]
      omega)]

theorem reuseRoot_ne_zero {mem : Mem} {nodes : List FreeNode} {need : UInt64}
    {choice : FreeChoice} (hList : FreeListAt mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice) : reuseRoot choice need ≠ 0 := by
  unfold reuseRoot
  split
  · rename_i hSplit
    obtain ⟨_, _, hBase, hRoot, _, _, _⟩ := split_facts hList hTake hSplit
    rw [← hRoot]
    intro hZero
    have := congrArg UInt64.toNat hZero
    rw [UInt64.toNat_add] at this
    simp only [UInt64.reduceToNat] at this
    omega
  · exact hList.roots_ne_zero _ (takeFirstFitFrom_some_mem hTake)

end Project.ProofKit
