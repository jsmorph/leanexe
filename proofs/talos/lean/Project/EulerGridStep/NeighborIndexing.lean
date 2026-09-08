import Project.EulerGridScan.Indexing

namespace Project.EulerGridStep.Execution
open Wasm

def previousOffset (index : Nat) : Nat := if index = 0 then 3 * index else 3 * index - 3

def nextOffset (size index : Nat) : Nat := if index + 1 < size / 3 then 3 * index + 3 else 3 * index

/-- Every conservative field of each clamped neighbor belongs to the old grid. -/
theorem neighbor_word_bounds (input : Array UInt64) (index field : Nat)
    (hi : index < input.size / 3) (hf : field < 3) :
    previousOffset index + field < input.size ∧ 3 * index + field < input.size ∧
      nextOffset input.size index + field < input.size := by
  unfold previousOffset nextOffset
  split_ifs <;> omega

/-- Checked word addition cannot wrap for these bounded grid offsets. -/
theorem neighbor_add_guard (offset amount : Nat) (ho : offset < 4294967296) (ha : amount ≤ 3) :
    ¬ (UInt64.ofNat offset + UInt64.ofNat amount < UInt64.ofNat offset) := by
  have hs : offset + amount < UInt64.size := by change offset + amount < 18446744073709551616; omega
  have hx : offset < UInt64.size := by omega
  rw [← UInt64.ofNat_add, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat_of_lt' hs, UInt64.toNat_ofNat_of_lt' hx]
  omega

theorem next_cell_word_test (size index : Nat) (hs : size < 4294967296) (hi : index < size / 3) :
    (UInt64.ofNat index + 1 < UInt64.ofNat size / 3) ↔ index + 1 < size / 3 := by
  have hAdd : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := (UInt64.ofNat_add index 1).symm
  have hDiv : UInt64.ofNat size / 3 = UInt64.ofNat (size / 3) :=
    (UInt64.ofNat_div (by change size < 18446744073709551616; omega) (by decide : 3 < 2 ^ 64)).symm
  rw [hAdd, hDiv, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat_of_lt' (by change index + 1 < 18446744073709551616; omega),
    UInt64.toNat_ofNat_of_lt' (by change size / 3 < 18446744073709551616; omega)]

 theorem cellAt_neighbors (ratio : UInt64) (input : Array UInt64) (index : Nat) :
    Model.cellAt ratio input index = Project.EulerCellStep.Model.cellCheckedBits ratio
      (input.getD (previousOffset index) 0) (input.getD (previousOffset index + 1) 0)
      (input.getD (previousOffset index + 2) 0) (input.getD (3 * index) 0)
      (input.getD (3 * index + 1) 0) (input.getD (3 * index + 2) 0)
      (input.getD (nextOffset input.size index) 0) (input.getD (nextOffset input.size index + 1) 0)
      (input.getD (nextOffset input.size index + 2) 0) := by
  simp [Model.cellAt, previousOffset, nextOffset]

#print axioms neighbor_word_bounds
#print axioms neighbor_add_guard
#print axioms next_cell_word_test
#print axioms cellAt_neighbors
end Project.EulerGridStep.Execution
