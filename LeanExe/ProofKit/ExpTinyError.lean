import LeanExe.ProofKit.RealExpError
import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64NearestBinade
import LeanExe.ProofKit.F64Bits

namespace LeanExe.ProofKit.ExpTinyError
open CodeLib.IEEE64 F64NearestNonnegative F64NearestEven F64NearestBinade

set_option exponentiation.threshold 4096

def result (x : UInt64) : UInt64 := Wasm.IEEE64.add 0x3FF0000000000000 x

theorem one_value : value 0x3FF0000000000000 = 1 := by
  have h : Wasm.IEEE64.scaledValue (0x3FF0000000000000 : UInt64) = (2 : Int) ^ 1074 := by
    decide +kernel
  rw [value, h]
  norm_num

theorem tiny_bounds (x : UInt64) (hxf : CodeLib.IEEE64.Finite x)
    (hx : |value x| ≤ 1 / (2 : ℝ) ^ 54) :
    CodeLib.IEEE64.Finite (result x) ∧
    1 / 2 ≤ Real.exp (value x) ∧ Real.exp (value x) ≤ 2 ∧
    1 / 2 ≤ value (result x) ∧ value (result x) ≤ 2 ∧
    |value (result x) - Real.exp (value x)| < 3 * unitRoundoff64 / 2 := by
  let a := value x
  have ha : |a| ≤ 1 / (2 : ℝ) ^ 54 := hx
  have ha1 : |a| ≤ 1 := ha.trans (by norm_num)
  have hsum : |1 + a| ≤ 1 + 1 / (2 : ℝ) ^ 54 := by
    have h := abs_add_le (1 : ℝ) a
    norm_num only [abs_one] at h
    linarith
  have hrec := F64AddBounds.add_real_relative 0x3FF0000000000000 x
    (by unfold CodeLib.IEEE64.Finite; decide) hxf (by
      rw [one_value]
      exact hsum.trans_lt (by norm_num))
  change CodeLib.IEEE64.Finite (result x) ∧
    |value (result x) - (value 0x3FF0000000000000 + a)| ≤
      unitRoundoff64 * |value 0x3FF0000000000000 + a| at hrec
  rw [one_value] at hrec
  have hsq : a ^ 2 ≤ (1 / (2 : ℝ) ^ 54) ^ 2 := by
    rw [← sq_abs]
    gcongr
  have ht := Real.abs_exp_sub_one_sub_id_le ha1
  have htay : |1 + a - Real.exp a| ≤ (1 / (2 : ℝ) ^ 54) ^ 2 := by
    have hid : 1 + a - Real.exp a = -(Real.exp a - 1 - a) := by ring
    rw [hid, abs_neg]
    exact ht.trans hsq
  have hunit : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have herr : |value (result x) - Real.exp a| ≤ (9 / 8) * unitRoundoff64 := by
    calc
      _ ≤ unitRoundoff64 * |1 + a| + (1 / (2 : ℝ) ^ 54) ^ 2 :=
        (abs_sub_le _ (1 + a) _).trans (add_le_add hrec.2 htay)
      _ ≤ unitRoundoff64 * (1 + 1 / (2 : ℝ) ^ 54) + (1 / (2 : ℝ) ^ 54) ^ 2 :=
        add_le_add (mul_le_mul_of_nonneg_left hsum hunit) le_rfl
      _ ≤ _ := by norm_num [unitRoundoff64]
  have he := Real.exp_bound ha1 (n := 1) (by decide)
  norm_num [Finset.sum_range_succ] at he
  have he' := abs_le.mp he
  have helo : 3 / 4 ≤ Real.exp a := by
    have hb : |a| ≤ 1 / 8 := ha.trans (by norm_num)
    linarith
  have hehi : Real.exp a ≤ 5 / 4 := by
    have hb : |a| ≤ 1 / 8 := ha.trans (by norm_num)
    linarith
  have hm : |value (result x) - Real.exp a| ≤ 1 / 4 :=
    herr.trans (by norm_num [unitRoundoff64])
  have hm' := abs_le.mp hm
  have hstrict : (9 / 8 : ℝ) * unitRoundoff64 < 3 * unitRoundoff64 / 2 := by
    norm_num [unitRoundoff64]
  refine ⟨hrec.1, ?_, ?_, ?_, ?_, herr.trans_lt hstrict⟩
  all_goals linarith

theorem tiny_one_step (x : UInt64) (hxf : CodeLib.IEEE64.Finite x)
    (hx : |value x| ≤ 1 / (2 : ℝ) ^ 54) :
    let w := roundNearestEven (Real.exp (value x))
    (result x).toNat ≤ w.toNat + 1 ∧ w.toNat ≤ (result x).toNat + 1 := by
  have hb := tiny_bounds x hxf hx
  have hlo : value (UInt64.ofNat (1022 * 2 ^ 52)) = (1 / 2 : ℝ) := by
    have h := boundary_power 1022 (-1) (by decide) (by decide) (by decide)
    norm_num at h
    exact h
  have hhi : value (UInt64.ofNat (1024 * 2 ^ 52)) = (2 : ℝ) := by
    have h := boundary_power 1024 1 (by decide) (by decide) (by decide)
    norm_num at h
    exact h
  have hg : (2 : ℝ) ^ (1022 - 1) / (2 : ℝ) ^ 1074 = unitRoundoff64 := by
    rw [power_quotient_split (1022 - 1) 53 0 (by decide)]
    norm_num [unitRoundoff64]
  apply one_step_normal_interval (Real.exp (value x)) (result x)
    (roundNearestEven (Real.exp (value x))) 1022 1024
    (by decide) (by decide) (by decide) (by decide) hb.1
    (roundNearestEven_spec _).1
  · rw [hlo, hhi]
    exact ⟨hb.2.1, hb.2.2.1⟩
  · rw [hlo, hhi]
    exact ⟨hb.2.2.2.1, hb.2.2.2.2.1⟩
  · rw [hg]
    exact hb.2.2.2.2.2

theorem float_result_bits (x : Float) : (1.0 + x).toBits = result x.toBits := by
  rw [F64Bits.toBits_add]
  rfl

#print axioms tiny_bounds
#print axioms tiny_one_step
#print axioms float_result_bits

end LeanExe.ProofKit.ExpTinyError
