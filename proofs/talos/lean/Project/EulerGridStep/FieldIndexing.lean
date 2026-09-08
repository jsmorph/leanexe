import Project.EulerGridStep.FieldMemory
import Project.ProofKit.FixedArrayCapacity

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit

theorem six_mul_guard (index : Nat) (hBound : index < 4294967296) (hPositive : 0 < index) :
    ¬ ((-1 : UInt64) / UInt64.ofNat index < 6) := by
  have h64 : index < UInt64.size := by change index < 18446744073709551616; omega
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_div, UInt64.toNat_ofNat_of_lt' h64]
  change ¬ 18446744073709551615 / index < 6
  apply Nat.not_lt.mpr
  apply (Nat.le_div_iff_mul_le hPositive).mpr
  omega

theorem small_add_guard (left right : Nat) (hSum : left + right < 4294967296) :
    ¬ (UInt64.ofNat left + UInt64.ofNat right < UInt64.ofNat left) := by
  have h64 : left + right < UInt64.size := by change left + right < 18446744073709551616; omega
  rw [← UInt64.ofNat_add, UInt64.lt_iff_toNat_lt,
    UInt64.toNat_ofNat_of_lt' h64, UInt64.toNat_ofNat_of_lt' (by omega : left < UInt64.size)]
  omega

theorem field_index_word (index field : Nat) :
    (1 : UInt64) + 6 * UInt64.ofNat index + UInt64.ofNat field =
      UInt64.ofNat (1 + 6 * index + field) := by
  have hMul : (6 : UInt64) * UInt64.ofNat index = UInt64.ofNat (6 * index) :=
    (UInt64.ofNat_mul 6 index).symm
  have hAdd : (1 : UInt64) + UInt64.ofNat (6 * index) = UInt64.ofNat (1 + 6 * index) :=
    (UInt64.ofNat_add 1 (6 * index)).symm
  rw [hMul, hAdd]
  exact (UInt64.ofNat_add (1 + 6 * index) field).symm

theorem scalar_capacity_word (count : Nat) (hBound : 8 * (count + 1) ≤ 4294967296) :
    FixedArrayCapacity.normalizedCapacity (UInt64.ofNat count) 1 =
      UInt64.ofNat (8 * (count + 1)) := by
  have hNumerator : 8 + count * 8 + 7 < UInt64.size := by
    change 8 + count * 8 + 7 < 18446744073709551616
    omega
  have hSum : (8 : UInt64) + UInt64.ofNat count * 8 + 7 = UInt64.ofNat (8 + count * 8 + 7) := by
    have hMul : UInt64.ofNat count * 8 = UInt64.ofNat (count * 8) :=
      (UInt64.ofNat_mul count 8).symm
    have hAdd : (8 : UInt64) + UInt64.ofNat (count * 8) = UInt64.ofNat (8 + count * 8) :=
      (UInt64.ofNat_add 8 (count * 8)).symm
    rw [hMul, hAdd]
    exact (UInt64.ofNat_add (8 + count * 8) 7).symm
  have hDivide : UInt64.ofNat (8 + count * 8 + 7) / 8 = UInt64.ofNat ((8 + count * 8 + 7) / 8) :=
    (UInt64.ofNat_div hNumerator (by decide)).symm
  have hNatural : (8 + count * 8 + 7) / 8 * 8 = 8 * (count + 1) := by omega
  have hRaw : FixedArrayCapacity.unnormalizedCapacity (UInt64.ofNat count) 1 =
      UInt64.ofNat (8 * (count + 1)) := by
    unfold FixedArrayCapacity.unnormalizedCapacity
    rw [UInt64.mul_one, hSum, hDivide]
    exact (UInt64.ofNat_mul ((8 + count * 8 + 7) / 8) 8).symm.trans (congrArg UInt64.ofNat hNatural)
  have hCapacity64 : 8 * (count + 1) < UInt64.size := by
    change 8 * (count + 1) < 18446744073709551616
    omega
  have hNotSmall : ¬ UInt64.ofNat (8 * (count + 1)) < 8 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hCapacity64]
    change ¬ 8 * (count + 1) < 8
    omega
  simp only [FixedArrayCapacity.normalizedCapacity, hRaw, ite_eq_right hNotSmall]

#print axioms six_mul_guard
#print axioms small_add_guard
#print axioms field_index_word
#print axioms scalar_capacity_word
end Project.EulerGridStep.Execution
