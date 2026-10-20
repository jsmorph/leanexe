import LeanExe.Pipeline.Records

namespace LeanExe.Pipeline

open Wasm

theorem block_pointer {store : Store Unit} {ptr : UInt64} (h : 48 ≤ ptr.toNat) :
    UInt64.ofNat ((block store ptr).1 + 48) = ptr := by
  simp only [block, Nat.sub_add_cancel h, UInt64.ofNat_toNat]

mutual
theorem NodeOwned.pointers_from_blocks {heap : Heap} {store : Store Unit} :
    ∀ (ptr : UInt64) (value : Node), NodeOwned heap store ptr value →
      (value.blocks store ptr).map (fun b => UInt64.ofNat (b.1 + 48)) =
        value.pointers store ptr
  | _, .null, _ => rfl
  | ptr, .record slots, ⟨hHeader, hSlots⟩ => by
    have hBase := hHeader.base
    simp only [Node.blocks, Node.pointers, List.map_cons, block_pointer (by omega : 48 ≤ ptr.toNat),
      SlotsOwned.pointers_from_blocks ptr 0 slots hSlots]

theorem SlotsOwned.pointers_from_blocks {heap : Heap} {store : Store Unit} :
    ∀ (ptr : UInt64) (i : Nat) (slots : List Slot), SlotsOwned heap store ptr i slots →
      (slotsBlocks store ptr i slots).map (fun b => UInt64.ofNat (b.1 + 48)) =
        slotsPointers store ptr i slots
  | _, _, [], _ => rfl
  | ptr, i, .word _ :: rest, ⟨_, hRest⟩ =>
    SlotsOwned.pointers_from_blocks ptr (i + 1) rest hRest
  | ptr, i, .child value :: rest, ⟨hChild, hRest⟩ => by
    simp only [slotsBlocks, slotsPointers, List.map_append,
      NodeOwned.pointers_from_blocks _ value hChild,
      SlotsOwned.pointers_from_blocks ptr (i + 1) rest hRest]
end

end LeanExe.Pipeline
