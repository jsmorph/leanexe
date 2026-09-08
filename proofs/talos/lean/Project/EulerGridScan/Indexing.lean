import Project.EulerGridScan.Helpers

namespace Project.EulerGridScan.Execution
open Wasm
set_option maxHeartbeats 1000000

theorem cellWord_lt (input : Array UInt64) (index field : Nat)
    (hi : index < input.size / 3) (hf : field < 3) : 3 * index + field < input.size := by
  omega

theorem input_size_lt_32 (initial : Store Unit) (pointer : UInt64) (input : Array UInt64)
    (h : Project.ProofKit.UInt64Array.At initial pointer input) : input.size < 4294967296 := by
  have hb := h.1
  omega

/-- A grid index fitting linear memory cannot overflow the checked triple offset. -/
theorem triple_mul_guard (index : Nat) (hbound : index < 4294967296) (hpos : 0 < index) :
    ¬ ((-1 : UInt64) / UInt64.ofNat index < 3) := by
  have h64 : index < UInt64.size := by change index < 18446744073709551616; omega
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' h64]
  change ¬ 18446744073709551615 / index < 3
  apply Nat.not_lt.mpr
  apply (Nat.le_div_iff_mul_le hpos).mpr
  omega

theorem triple_mul_word (index : Nat) :
    (3 : UInt64) * UInt64.ofNat index = UInt64.ofNat (3 * index) := by
  exact (UInt64.ofNat_mul 3 index).symm

theorem offset_add_guard (offset field : Nat) (ho : offset < 4294967296) (hf : field < 3) :
    ¬ (UInt64.ofNat offset + UInt64.ofNat field < UInt64.ofNat offset) := by
  have hsum : offset + field < UInt64.size := by
    change offset + field < 18446744073709551616
    omega
  have h64 : offset < UInt64.size := by omega
  rw [← UInt64.ofNat_add, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat_of_lt' hsum, UInt64.toNat_ofNat_of_lt' h64]
  omega

theorem index_word_lt (input : Array UInt64) (index : Nat) (hsize : input.size < UInt64.size)
    (hi : index < input.size) : UInt64.ofNat index < UInt64.ofNat input.size := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega),
    UInt64.toNat_ofNat_of_lt' hsize]
  exact hi

/-- Shared load facts for the source's total reads at known-valid indices. -/
theorem arrayRead_facts (initial : Store Unit) (pointer : UInt64) (input : Array UInt64)
    (h : Project.ProofKit.UInt64Array.At initial pointer input) (index : Nat) (hi : index < input.size) :
    (UInt64.ofNat index).toNat = index ∧ UInt64.ofNat index < UInt64.ofNat input.size ∧
    (pointer.toNat + (index + 1) * 8) % 4294967296 + 8 ≤ initial.mem.pages * 65536 ∧
    initial.mem.read64 (UInt32.ofNat ((pointer.toNat + (index + 1) * 8) % 4294967296)) =
      input.getD index 0 := by
  have hsize := h.size_lt
  refine ⟨UInt64.toNat_ofNat_of_lt' (by omega), index_word_lt _ _ hsize hi, (h.generatedElement index hi).1, ?_⟩
  simpa [Nat.mul_comm, Array.getD, hi] using (h.generatedElement index hi).2

#print axioms triple_mul_guard
#print axioms offset_add_guard
#print axioms arrayRead_facts
end Project.EulerGridScan.Execution
