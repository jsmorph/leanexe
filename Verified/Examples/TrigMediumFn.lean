import LeanExe.ProofKit.F64SignedNearestSum
import Verified.Examples.TrigLargeFloat
import Verified.Examples.TrigPi
import LeanExe.ProofKit.F64ArithmeticBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
The count of `π/2` in fdlibm's medium reduction.  `fn = (x · invpio2 + 1.5 · 2 ^ 52) - 1.5 · 2 ^ 52`
in rounded arithmetic is the integer `N` nearest to the rounded product: the sum lies in
`[2 ^ 52, 2 ^ 53)`, where the doubles are the integers, and the rounded sum is nearest.  For
`1 ≤ x` and `x · 2/π ≤ 2 ^ 20`, `N` is from 1 to `2 ^ 20` and within `1/2 + 2 ^ -30` of `x · 2/π`.
-/

namespace Verified.Examples.TrigMediumFn

open CodeLib.IEEE64 LeanExe.ProofKit F64ValueExact F64SignedNearestSum TrigPi

/-- 53 bits of `2/π`. -/
def invpio2 : UInt64 := 0x3FE45F306DC9C883

/-- `1.5 · 2 ^ 52`. -/
def shifter : UInt64 := 0x4338000000000000

set_option exponentiation.threshold 4096 in
theorem invpio2_checked :
    (tableNum : Int) - 2 ^ 1162 ≤ Wasm.IEEE64.scaledValue invpio2 * 2 ^ 142 ∧
      Wasm.IEEE64.scaledValue invpio2 * 2 ^ 142 ≤ (tableNum : Int) + 2 ^ 1162 := by
  decide +kernel

theorem invpio2_close : |value invpio2 - 2 / Real.pi| ≤ 1 / 2 ^ 53 := by
  obtain ⟨h1, h2⟩ := invpio2_checked
  obtain ⟨t1, t2⟩ := table_bounds
  have hv : value invpio2 = ((Wasm.IEEE64.scaledValue invpio2 * 2 ^ 142 : Int) : ℝ) / 2 ^ 1216 := by
    simp only [value]
    rw [show (2 : ℝ) ^ 1216 = 2 ^ 1074 * 2 ^ 142 by rw [← pow_add]]
    push_cast
    field_simp
    norm_num
  generalize Wasm.IEEE64.scaledValue invpio2 * 2 ^ 142 = S at h1 h2 hv
  generalize tableNum = T at h1 h2 t1 t2
  have h1' : (T : ℝ) ≤ (S : ℝ) + 2 ^ 1162 := by
    have : (T : Int) ≤ S + 2 ^ 1162 := by linarith
    exact_mod_cast this
  have h2' : (S : ℝ) ≤ (T : ℝ) + 2 ^ 1162 := by exact_mod_cast h2
  have hp : (0 : ℝ) < 2 ^ 1216 := by positivity
  have h54 : (2 : ℝ) ^ 1162 / 2 ^ 1216 = 1 / 2 ^ 54 := by
    rw [div_eq_div_iff (by positivity) (by positivity), one_mul, ← pow_add]
  have h1216 : (1 : ℝ) / 2 ^ 1216 ≤ 1 / 2 ^ 54 := by
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by norm_num)
  have hT1 : (T : ℝ) / 2 ^ 1216 ≤ 2 / Real.pi := by
    rw [div_le_iff₀ hp]
    linarith
  have hT2 : 2 / Real.pi ≤ (T : ℝ) / 2 ^ 1216 + 1 / 2 ^ 1216 := by
    rw [← add_div, le_div_iff₀ hp]
    linarith
  have hA : (S : ℝ) / 2 ^ 1216 ≤ (T : ℝ) / 2 ^ 1216 + 1 / 2 ^ 54 := by
    rw [← h54, ← add_div]
    exact div_le_div_of_nonneg_right h2' hp.le
  have hB : (T : ℝ) / 2 ^ 1216 ≤ (S : ℝ) / 2 ^ 1216 + 1 / 2 ^ 54 := by
    rw [← h54, ← add_div]
    exact div_le_div_of_nonneg_right h1' hp.le
  have h5354 : (1 : ℝ) / 2 ^ 54 + 1 / 2 ^ 54 = 1 / 2 ^ 53 := by norm_num
  rw [hv, abs_le]
  constructor <;> linarith

theorem shifter_facts : Finite shifter ∧
    Wasm.IEEE64.scaledValue shifter = 6755399441055744 * 2 ^ 1074 := by
  unfold CodeLib.IEEE64.Finite
  constructor <;> decide +kernel

theorem invpio2_finite : Finite invpio2 := by
  unfold CodeLib.IEEE64.Finite
  decide

/-- The count `fn` of fdlibm's medium reduction. -/
theorem fn_spec (x : UInt64) (hxf : Finite x) (hx1 : 1 ≤ value x)
    (hx2 : value x * (2 / Real.pi) ≤ 2 ^ 20) :
    Finite (Wasm.IEEE64.sub (Wasm.IEEE64.add (Wasm.IEEE64.mul x invpio2) shifter) shifter) ∧
      ∃ N : Nat, 1 ≤ N ∧ N ≤ 2 ^ 20 ∧
        Wasm.IEEE64.scaledValue
            (Wasm.IEEE64.sub (Wasm.IEEE64.add (Wasm.IEEE64.mul x invpio2) shifter) shifter) =
          (N : Int) * 2 ^ 1074 ∧
        |(N : ℝ) - value x * (2 / Real.pi)| ≤ 1 / 2 + 1 / 2 ^ 30 := by
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi2 : Real.pi < 3.15 := Real.pi_lt_d2
  have hinv := invpio2_close
  rw [abs_le] at hinv
  have hsf := shifter_facts.1
  have hsval : value shifter = 6755399441055744 := by
    have hsv := shifter_facts.2
    simp only [value, hsv]
    push_cast
    field_simp
  have hds : (2 : Int) ^ 1074 ∣ Wasm.IEEE64.scaledValue shifter :=
    ⟨6755399441055744, by rw [shifter_facts.2]; ring⟩
  have h2pi : 2 / Real.pi ≤ 2 / 3 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have h2pi' : 0.6 ≤ 2 / Real.pi := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  -- The rounded product `t0`.
  have hxinv : |value x * value invpio2| ≤ 2 ^ 21 := by
    have hv0 : 0 ≤ value invpio2 := by linarith
    rw [abs_mul, abs_of_pos (by linarith), abs_of_nonneg hv0]
    have : value invpio2 ≤ 2 / Real.pi * 2 := by nlinarith
    nlinarith
  have h1022 : (2 : ℝ) ^ 21 < 2 ^ 1022 := pow_lt_pow_right₀ (by norm_num) (by norm_num)
  obtain ⟨ht0f, ht0e⟩ := F64ArithmeticBounds.mul_error x invpio2 hxf invpio2_finite (2 ^ 21)
    (one_le_pow₀ (by norm_num)) h1022 hxinv
  generalize Wasm.IEEE64.mul x invpio2 = t0 at ht0f ht0e ⊢
  have hae : arithmeticEpsilon * 2 ^ 21 = 1 / 2 ^ 31 := by
    norm_num [arithmeticEpsilon]
  rw [hae] at ht0e
  have ht0x : |value t0 - value x * (2 / Real.pi)| ≤ 1 / 2 ^ 30 := by
    have h1 : |value x * value invpio2 - value x * (2 / Real.pi)| ≤ value x * (1 / 2 ^ 53) := by
      rw [← mul_sub, abs_mul, abs_of_pos (by linarith)]
      exact mul_le_mul_of_nonneg_left (by rw [abs_le]; constructor <;> linarith) (by linarith)
    have hx3 : value x ≤ 2 ^ 21 := by nlinarith
    have h2 : value x * (1 / 2 ^ 53) ≤ 1 / 2 ^ 32 := by
      calc value x * (1 / 2 ^ 53) ≤ 2 ^ 21 * (1 / 2 ^ 53) :=
            mul_le_mul_of_nonneg_right hx3 (by norm_num)
        _ = 1 / 2 ^ 32 := by norm_num
    have := abs_sub_le (value t0) (value x * value invpio2) (value x * (2 / Real.pi))
    have : (1 : ℝ) / 2 ^ 31 + 1 / 2 ^ 32 ≤ 1 / 2 ^ 30 := by norm_num
    linarith
  rw [abs_le] at ht0x
  have hxpos : 0.6 ≤ value x * (2 / Real.pi) := by nlinarith
  have hsmall : (1 : ℝ) / 2 ^ 30 ≤ 1 / 100 := by norm_num
  -- The rounded sum `t1` is the nearest integer.
  set V := value t0 + value shifter with hV
  have hVlo : 6755399441055744 + 1 / 2 ≤ V := by rw [hV, hsval]; linarith
  have hVhi : V ≤ 6755399441055744 + 2 ^ 20 + 1 := by rw [hV, hsval]; linarith
  have hV53 : V < 2 ^ 53 := by
    have : (6755399441055744 : ℝ) + 2 ^ 20 + 1 < 2 ^ 53 := by norm_num
    linarith
  have hV1023 : |V| < 2 ^ 1023 := by
    rw [abs_of_pos (by linarith)]
    exact lt_trans hV53 (pow_lt_pow_right₀ (by norm_num) (by norm_num))
  have hfl : 0 ≤ Int.floor (V + 1 / 2) := by
    apply Int.floor_nonneg.mpr
    linarith
  set m := (Int.floor (V + 1 / 2)).toNat with hm
  have hmc : (m : ℝ) = ((Int.floor (V + 1 / 2) : Int) : ℝ) := by
    have h : ((m : Int) : ℝ) = ((Int.floor (V + 1 / 2) : Int) : ℝ) := by
      rw [hm, Int.toNat_of_nonneg hfl]
    exact_mod_cast h
  have hmV : |(m : ℝ) - V| ≤ 1 / 2 := by
    have h1 := Int.floor_le (V + 1 / 2)
    have h2 := Int.lt_floor_add_one (V + 1 / 2)
    rw [hmc, abs_le]
    constructor <;> linarith
  have hm53 : m < 2 ^ 53 := by
    have h : (m : ℝ) < 2 ^ 53 := by
      have := (abs_le.mp hmV).2
      linarith
    exact_mod_cast h
  have hm64 : m < 2 ^ 64 := lt_trans hm53 (by norm_num)
  obtain ⟨hcf, hcs, hcm⟩ := TrigLargeFloat.convert_exact (UInt64.ofNat m) (by
    rw [UInt64.toNat_ofNat_of_lt' hm64]
    exact hm53)
  have hcv : value (Wasm.IEEE64.convertI64U (UInt64.ofNat m)) = m := by
    simp only [value, Wasm.IEEE64.scaledValue, hcs, Bool.false_eq_true, ite_false, hcm,
      UInt64.toNat_ofNat_of_lt' hm64]
    push_cast
    field_simp
  have hnear := add_nearest t0 shifter ht0f hsf hV1023 (Wasm.IEEE64.convertI64U (UInt64.ofNat m))
  rw [hcv, ← hV] at hnear
  have ht1 := hnear.trans hmV
  obtain ⟨ht1f, -⟩ := add_rel t0 shifter ht0f hsf hV1023
  generalize Wasm.IEEE64.add t0 shifter = t1 at ht1 ht1f hnear ⊢
  rw [abs_le] at ht1
  have e1 : (2 : ℝ) ^ (52 + 1074) / 2 ^ 1074 = 2 ^ 52 := by
    rw [pow_add]
    field_simp
  have e2 : (2 : ℝ) ^ (53 + 1074) / 2 ^ 1074 = 2 ^ 53 := by
    rw [pow_add]
    field_simp
  have hd1 : (2 : Int) ^ 1074 ∣ Wasm.IEEE64.scaledValue t1 := by
    apply dvd_of_value t1 ht1f 1074
    rw [e1, abs_of_pos (by linarith)]
    have : (2 : ℝ) ^ 52 ≤ 6755399441055744 := by norm_num
    linarith
  obtain ⟨hff, hfv⟩ := sub_exact t1 shifter ht1f hsf 1074 (by norm_num) hd1 hds (by
    rw [hsval, e2, abs_le]
    have : (2 : ℝ) ^ 20 + 2 ≤ 2 ^ 53 := by norm_num
    constructor <;> linarith)
  refine ⟨hff, ?_⟩
  have hsd := scaled_of_value_sub t1 shifter _ hfv
  have hdf : (2 : Int) ^ 1074 ∣ Wasm.IEEE64.scaledValue
      (Wasm.IEEE64.sub t1 shifter) := by
    rw [hsd]
    exact dvd_sub hd1 hds
  obtain ⟨K, hK⟩ := hdf
  have hKv : value (Wasm.IEEE64.sub t1 shifter) = K := by
    simp only [value, hK]
    push_cast
    field_simp
  rw [hKv, hsval] at hfv
  have hKr1 : (K : ℝ) - value t0 ≤ 1 / 2 := by linarith
  have hKr2 : -(1 / 2) ≤ (K : ℝ) - value t0 := by linarith
  have hK1 : 1 ≤ K := by
    have : (0 : ℝ) < K := by linarith
    have : 0 < K := by exact_mod_cast this
    omega
  have hK2 : K ≤ 2 ^ 20 := by
    have : (K : ℝ) < 2 ^ 20 + 1 := by linarith
    have : K < 2 ^ 20 + 1 := by exact_mod_cast this
    omega
  refine ⟨K.toNat, by omega, by omega, ?_, ?_⟩
  · rw [hK, mul_comm, Int.toNat_of_nonneg (by omega)]
  · have hKn : ((K.toNat : Nat) : ℝ) = (K : ℝ) := by
      have : ((K.toNat : Nat) : Int) = K := Int.toNat_of_nonneg (by omega)
      exact_mod_cast this
    rw [hKn, abs_le]
    constructor <;> linarith

#print axioms invpio2_close
#print axioms fn_spec

end Verified.Examples.TrigMediumFn
