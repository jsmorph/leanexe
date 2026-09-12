import Project.ClobMatchFuel.BookAllocFitState

namespace Project.ProofKit.FreeListMemory
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit Project.ProofKit.Memory

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

end Project.ProofKit.FreeListMemory
