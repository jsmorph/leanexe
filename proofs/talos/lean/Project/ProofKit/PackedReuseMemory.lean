import Project.ProofKit.PackedReuse
import Project.ProofKit.PackedMemory

namespace Project.ProofKit.PackedReuse
open Wasm Project.Runtime Project.ProofKit.Memory FixedArrayReuse

theorem freeListAt (store : Store Unit) (nodes : List FreeNode) (need : UInt64) (choice : FreeChoice)
    (hList : FreeListAt store.mem nodes) (hTake : takeFirstFitFrom 0 need nodes = some choice) :
    FreeListAt (reused store choice).mem choice.remaining := by
  obtain ⟨h48, h32, _⟩ := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
  have hBase : (choice.node.root - 48).toNat = choice.node.root.toNat - 48 :=
    toNat_sub_of_le _ _ h48
  have hUnlink := hList.unlink_takeFirstFitFrom hTake
  apply FreeListMemory.frame_headers (mem' := (reused store choice).mem) hUnlink (Nat.le_refl _)
  intro node hNode address hLow hHigh
  have hSep := hList.takeFirstFitFrom_node_disjoint hTake node hNode
  change (PackedHeader.headerMem (unlinkFreeChoice store.mem choice)
    (choice.node.root - 48) choice.node.capacity).bytes address = _
  apply PackedHeader.bytes_outside
  · rw [hBase]; omega
  · rw [hBase]
    unfold regionsDisjoint FreeNode.region at hSep
    omega

theorem unlink_bytes (store : Store Unit) (nodes : List FreeNode) (need : UInt64) (choice : FreeChoice)
    (lower upper address : Nat) (hList : FreeListAt store.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSep : ∀ node ∈ nodes, upper ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ lower)
    (hLow : lower ≤ address) (hHigh : address < upper) :
    (unlinkFreeChoice store.mem choice).bytes address = store.mem.bytes address := by
  by_cases hPrevious : choice.previous = 0
  · simp [unlinkFreeChoice, hPrevious]
  · obtain ⟨predecessor, hMem, hRoot⟩ := FreeListMemory.previous_mem hTake hPrevious
    obtain ⟨h48, h32, _⟩ := hList.mem_bounds hMem
    have hDisjoint := hSep predecessor hMem
    rw [unlinkFreeChoice, ite_eq_right hPrevious, hRoot]
    apply write64_bytes_outside
    rw [UInt64.toNat_toUInt32, toNat_sub_of_le _ _ (by change 8 ≤ predecessor.root.toNat; omega),
      Nat.mod_eq_of_lt (by omega)]
    change address < predecessor.root.toNat - 8 ∨ predecessor.root.toNat - 8 + 8 ≤ address
    omega

theorem bytes_outside (store : Store Unit) (nodes : List FreeNode) (need : UInt64) (choice : FreeChoice)
    (lower upper address : Nat) (hList : FreeListAt store.mem nodes)
    (hTake : takeFirstFitFrom 0 need nodes = some choice)
    (hSep : ∀ node ∈ nodes, upper ≤ node.root.toNat - 48 ∨
      node.root.toNat + node.capacity.toNat ≤ lower)
    (hLow : lower ≤ address) (hHigh : address < upper) :
    (reused store choice).mem.bytes address = store.mem.bytes address := by
  have hMem := takeFirstFitFrom_some_mem hTake
  obtain ⟨h48, h32, _⟩ := hList.mem_bounds hMem
  have hSepChoice := hSep choice.node hMem
  have hBase : (choice.node.root - 48).toNat = choice.node.root.toNat - 48 :=
    toNat_sub_of_le _ _ h48
  change (PackedHeader.headerMem (unlinkFreeChoice store.mem choice)
    (choice.node.root - 48) choice.node.capacity).bytes address = _
  rw [PackedHeader.bytes_outside _ _ _ (by rw [hBase]; omega) _ (by rw [hBase]; omega)]
  exact unlink_bytes store nodes need choice lower upper address hList hTake hSep hLow hHigh

#print axioms freeListAt
#print axioms bytes_outside

end Project.ProofKit.PackedReuse
