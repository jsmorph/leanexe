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
