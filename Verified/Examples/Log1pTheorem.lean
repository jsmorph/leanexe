import Verified.Examples.Log1pTheoremCorr

/-!
`Log1p.log1p x` within one step of `log (1 + x)` for every finite `x > -1`.  The proof follows the
code's branches on the high word.  Below `2 ^ -54` in magnitude the result is `x`, and below
`2 ^ -29` it is `x - x²/2`, both within the relative criterion.  On `[-0.2929, 0.4142)` the result
is `log1pTail x 0 0 1` (`Log1pTheoremK0`).  Elsewhere `u = 1 + x`, or `u = x` from `2 ^ 53` on,
is written as `2 ^ K (1 + f)` (`Log1pTheoremReduce.main_reduce`), the correction approximates
`t = (1 + x - u)/u` (`Log1pTheoremCorr`), and `Log1pTheoremTail` bounds the result against
`K log 2 + log (1 + f) + log (1 + t) = log (1 + x)`.  The single input `1 - 2 ^ -53`, where
`1 + x` rounds to 2 and the correction misses `t = -2 ^ -54`, has `f = 0`.
-/

namespace Verified.Examples.Log1pTheorem
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest Log1pTheoremBranches
  Log1pTheoremTail Log1pTheoremReduce Log1pTheoremCorr Log1pTheoremK0

set_option exponentiation.threshold 4096

theorem hx_nat (x : Float) :
    (hxOf x).toNat = x.toBits.toNat / 2 ^ 32 ∧
      (hxOf x >>> 31).toNat = x.toBits.toNat / 2 ^ 63 ∧
      (axOf x).toNat = x.toBits.toNat % 2 ^ 63 / 2 ^ 32 := by
  have hw := x.toBits.toNat_lt
  refine ⟨?_, ?_, ?_⟩
  · simp only [hxOf, UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
      Nat.shiftRight_eq_div_pow]
  · simp only [hxOf, UInt64.toNat_shiftRight, show (32 : UInt64).toNat % 64 = 32 from rfl,
      show (31 : UInt64).toNat % 64 = 31 from rfl, Nat.shiftRight_eq_div_pow,
      Nat.div_div_eq_div_mul]
    norm_num
  · exact F64UpperWord.high_toNat x.toBits

theorem hx_toNat (x : Float) : (hxOf x).toNat = x.toBits.toNat / 2 ^ 32 := (hx_nat x).1

theorem hx31_toNat (x : Float) : (hxOf x >>> 31).toNat = x.toBits.toNat / 2 ^ 63 :=
  (hx_nat x).2.1

theorem ax_toNat (x : Float) : (axOf x).toNat = x.toBits.toNat % 2 ^ 63 / 2 ^ 32 :=
  (hx_nat x).2.2

/-- Reduces a test on the high words to arithmetic on `x.toBits.toNat`. -/
macro "bits_omega" : tactic => `(tactic| (
  simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, Bool.not_eq_false', beq_iff_eq, beq_eq_false_iff_ne, bne_iff_ne,
    bne_eq_false_iff_eq, ne_eq, decide_eq_true_eq, decide_eq_false_iff_not, not_lt, not_le,
    ← UInt64.toNat_inj, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, hx_toNat, hx31_toNat,
    ax_toNat, UInt64.reduceToNat]
  omega))

/-- The magnitude test `ax < H` as a bound on `|x|`. -/
theorem ax_lt (x : Float) (H : ℕ) (hH : H < 2 ^ 31) (q : ℚ)
    (hq : PolyBound.ratOfWord (UInt64.ofNat (H * 2 ^ 32)) = q) :
    (axOf x).toNat < H ↔ |value x.toBits| < (q : ℝ) := by
  rw [axOf, hxOf, F64UpperWord.high_lt_iff x.toBits H hH,
    ← PolyBound.ratOfWord_cast (UInt64.ofNat (H * 2 ^ 32)), hq]

theorem sign_value (x : Float) (hx : Finite x.toBits) :
    (2 ^ 63 ≤ x.toBits.toNat → value x.toBits ≤ 0) ∧
      (x.toBits.toNat < 2 ^ 63 → 0 ≤ value x.toBits) := by
  constructor
  · intro h
    have hs : Wasm.IEEE64.sign x.toBits = true := by
      simp only [Wasm.IEEE64.sign, decide_eq_true_eq]
      exact h
    simp only [value, Wasm.IEEE64.scaledValue, hs, ite_true]
    apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
    push_cast
    linarith [(Nat.cast_nonneg (Wasm.IEEE64.scaledMagnitude x.toBits) : (0 : ℝ) ≤ _)]
  · intro h
    exact value_nonneg_of_lt _ h

/-- `|x| < 2 ^ -54`: the result `x`. -/
theorem tiny_within (x : Float) (hx : Finite x.toBits) (h : |value x.toBits| < 1 / 2 ^ 54) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits)) x.toBits := by
  refine F64WithinSelf.within_one_of_self x.toBits hx _ (1 / 2 ^ 53) (by positivity) le_rfl ?_
  have h1 := log_near_t (value x.toBits) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 54 ≤ 1 / 2)])
  rw [abs_sub_comm]
  refine h1.trans ?_
  rw [← sq_abs]
  have h2 : |value x.toBits| ^ 2 ≤ |value x.toBits| * (1 / 2 ^ 54) := by
    rw [sq]
    exact mul_le_mul_of_nonneg_left h.le (abs_nonneg _)
  linarith

/-- `2 ^ -54 ≤ |x| < 2 ^ -29`: the result `x - x * x * 0.5`. -/
theorem small_within (x : Float) (hx : Finite x.toBits) (h1 : 1 / 2 ^ 54 ≤ |value x.toBits|)
    (h2 : |value x.toBits| < 1 / 2 ^ 29) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits)) (x - x * x * 0.5).toBits := by
  set v := value x.toBits with hv
  set a := |v| with ha
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) h1
  have hfa : FApprox x v 0 := approx_self x.toBits hx
  have hxx := fapprox_mul hfa hfa a a le_rfl le_rfl (a * a) (by simp) (by nlinarith)
  simp only [zero_mul, mul_zero, add_zero, zero_add] at hxx
  have hh : FApprox (0.5 : Float) (1 / 2) 0 := by
    unfold FApprox
    rw [show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, ?_⟩
    rw [show value 0x3FE0000000000000 = 1 / 2 by
      rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x3FE0000000000000 = 1 / 2 by
        decide +kernel]; norm_num]
    norm_num
  have hvv : |v * v| ≤ a * a := by rw [abs_mul]
  have hq := fapprox_mul hxx hh (a * a) (1 / 2) hvv (by norm_num)
    ((a * a + (a * a / 2 ^ 53 + 1 / 2 ^ 1075)) * (1 / 2)) (by simp) (by nlinarith)
  simp only [mul_zero, add_zero, zero_add] at hq
  have hcub := log_cubic v (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 29 ≤ 1 / 2)])
  have hlt := log_near_t v (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 29 ≤ 1 / 2)])
  have hy : a * (1 - 1 / 2 ^ 28) ≤ |Real.log (1 + v)| := by
    have h3 := abs_sub_abs_le_abs_sub v (Real.log (1 + v))
    rw [abs_sub_comm] at hlt
    have h4 : v ^ 2 ≤ a * (1 / 2 ^ 29) := by
      rw [← sq_abs, sq]
      exact mul_le_mul_of_nonneg_left h2.le ha0.le
    have : (1 : ℝ) / 2 ^ 28 = 2 * (1 / 2 ^ 29) := by norm_num
    nlinarith
  have hv3 : |v ^ 3 / 3| + 2 * v ^ 4 ≤ a * (1 / 2 ^ 58) := by
    have h3 : a ^ 2 ≤ 1 / 2 ^ 58 := by
      have := mul_le_mul h2.le h2.le ha0.le (by positivity)
      nlinarith
    have e0 : |v ^ 3 / 3| = a ^ 3 / 3 := by
      rw [abs_div, abs_pow, ha]
      norm_num
    have e4 : v ^ 4 = a ^ 4 := by
      rw [ha, pow_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ v ^ 4)]
    have e1 : a ^ 3 ≤ a * (1 / 2 ^ 58) := by
      calc a ^ 3 = a * a ^ 2 := by ring
        _ ≤ a * (1 / 2 ^ 58) := mul_le_mul_of_nonneg_left h3 ha0.le
    have e2 : a ^ 4 ≤ a * (1 / 2 ^ 87) := by
      have h5 : a * a ^ 2 ≤ 1 / 2 ^ 29 * (1 / 2 ^ 58) :=
        mul_le_mul h2.le h3 (by positivity) (by positivity)
      calc a ^ 4 = a * (a * a ^ 2) := by ring
        _ ≤ a * (1 / 2 ^ 29 * (1 / 2 ^ 58)) := mul_le_mul_of_nonneg_left h5 ha0.le
        _ = a * (1 / 2 ^ 87) := by norm_num
    rw [e0, e4]
    have : (1 : ℝ) / 2 ^ 58 / 3 + 2 * (1 / 2 ^ 87) ≤ 1 / 2 ^ 58 := by norm_num
    nlinarith
  refine sub_within_rel hfa hq _ (1 / 2 ^ 56) (by positivity) (by norm_num) ?_ ?_ ?_
  · have hd : |v - v * v * (1 / 2) - Real.log (1 + v)| ≤ |v ^ 3 / 3| + 2 * v ^ 4 := by
      rw [show v - v * v * (1 / 2) - Real.log (1 + v) =
        -(v ^ 3 / 3) - (Real.log (1 + v) - (v - v ^ 2 / 2 + v ^ 3 / 3)) by ring]
      have := abs_sub (-(v ^ 3 / 3)) (Real.log (1 + v) - (v - v ^ 2 / 2 + v ^ 3 / 3))
      rw [abs_neg] at this
      linarith
    have he : (a * a / 2 ^ 53 + 1 / 2 ^ 1075) * (1 / 2) +
        (a * a + (a * a / 2 ^ 53 + 1 / 2 ^ 1075)) * (1 / 2) / 2 ^ 53 + 1 / 2 ^ 1075 ≤
          a * (1 / 2 ^ 70) := by
      have h3 : a * a ≤ a * (1 / 2 ^ 29) := mul_le_mul_of_nonneg_left h2.le ha0.le
      have h4 : (1 : ℝ) / 2 ^ 1075 ≤ a * (1 / 2 ^ 1000) := by nlinarith
      nlinarith
    have hρ : a * (1 / 2 ^ 70) + a * (1 / 2 ^ 58) ≤ 1 / 2 ^ 56 * (a * (1 - 1 / 2 ^ 28)) := by
      nlinarith
    have := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 56)
    linarith
  · have h3 : (1 : ℝ) / 2 ^ 1021 ≤ a * (1 - 1 / 2 ^ 28) := by nlinarith
    linarith
  · have h3 := abs_log_t v (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 29 ≤ 1 / 4)])
    have : (2 : ℝ) * (1 / 2 ^ 29) < 2 ^ 1021 := by norm_num
    linarith

theorem two54_sum (x : Float) (hx : Finite x.toBits) (h : |value x.toBits| < 1) :
    decide (Float.ofBits 0x4350000000000000 + x > 0.0) = true := by
  have hw : Finite (0x4350000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hv : value (0x4350000000000000 : UInt64) = 2 ^ 54 := by
    rw [← PolyBound.ratOfWord_cast, show PolyBound.ratOfWord 0x4350000000000000 = 2 ^ 54 by
      decide +kernel]
    norm_num
  have hs := fapprox_add (fapprox_ofBits _ hw) (approx_self x.toBits hx) (2 ^ 54 + 1)
    (by rw [hv]; have := abs_add_le (2 ^ 54 : ℝ) (value x.toBits); norm_num at this ⊢; linarith)
    (by norm_num)
  rw [hv] at hs
  have h0 : Finite (0.0 : Float).toBits := by
    rw [show (0.0 : Float).toBits = 0 from rfl]; unfold CodeLib.IEEE64.Finite; decide
  rw [decide_eq_true_eq, gt_iff_lt, F64UpperWord.float_lt_iff _ _ h0 hs.1, zero_bits_value]
  have := hs.lower
  have h2 := (abs_lt.mp h).1
  norm_num at this ⊢
  linarith

/-- The branch for `|x| < 2 ^ -29`. -/
theorem branch_tiny (x : Float) (hx : Finite x.toBits)
    (hs : (hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) = true)
    (c1 : (axOf x).toNat < 0x3e200000) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits)) (Log1p.log1p x).toBits := by
  rw [log1p_tiny_eq x hs (UInt64.lt_iff_toNat_lt.mpr (by simpa using c1))]
  have h29 := (ax_lt x 0x3e200000 (by norm_num) (1 / 2 ^ 29) (by decide +kernel)).mp c1
  push_cast at h29
  rw [two54_sum x hx (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 29 < 1)]), Bool.true_and]
  by_cases c0 : (axOf x).toNat < 0x3c900000
  · have h54 := (ax_lt x 0x3c900000 (by norm_num) (1 / 2 ^ 54) (by decide +kernel)).mp c0
    push_cast at h54
    have hc : (decide (axOf x < 0x3c900000)) = true := by
      rw [decide_eq_true_eq, UInt64.lt_iff_toNat_lt]
      simpa using c0
    rw [hc, if_pos rfl]
    exact tiny_within x hx h54
  · have h54 : ¬ |value x.toBits| < ((1 / 2 ^ 54 : ℚ) : ℝ) :=
      fun h => c0 ((ax_lt x 0x3c900000 (by norm_num) (1 / 2 ^ 54) (by decide +kernel)).mpr h)
    push_cast at h54
    have hc : (decide (axOf x < 0x3c900000)) = false := by
      rw [decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt]
      simpa using c0
    rw [hc, if_neg (by simp)]
    exact small_within x hx (not_lt.mp h54) h29

theorem K_cases (K : ℤ) (h1 : -60 ≤ K) (h2 : K ≤ 1024) (h0 : K ≠ 0) :
    (K : ℝ) = 1 ∨ (K : ℝ) = -1 ∨ (2 ≤ |(K : ℝ)| ∧ |(K : ℝ)| ≤ 1100) := by
  rcases (by omega : K = 1 ∨ K = -1 ∨ 2 ≤ K ∨ K ≤ -2) with h | h | h | h
  · left; rw [h]; norm_num
  · right; left; rw [h]; norm_num
  · right; right
    have h3 : (2 : ℝ) ≤ K := by exact_mod_cast h
    have h4 : (K : ℝ) ≤ 1024 := by exact_mod_cast h2
    rw [abs_of_pos (by linarith)]
    constructor <;> linarith
  · right; right
    have h3 : (K : ℝ) ≤ -2 := by exact_mod_cast h
    have h4 : (-60 : ℝ) ≤ K := by exact_mod_cast h1
    rw [abs_of_neg (by linarith)]
    constructor <;> linarith

/-- The main path from the correction's bound, for `K ≠ 0` with `t` and `c` small. -/
theorem main_finish (x u c : Float) (hdom : -1 < value x.toBits) (hu : Finite u.toBits)
    (hpos : 1 / 2 ^ 60 ≤ value u.toBits)
    (hfar : value u.toBits < 1482910 / 2097152 ∨ 14142132 / 10 ^ 7 ≤ value u.toBits) (et : ℝ)
    (hc : FApprox c ((1 + value x.toBits - value u.toBits) / value u.toBits) et)
    (ht : |(1 + value x.toBits - value u.toBits) / value u.toBits| ≤ 1 / 2 ^ 52)
    (het : et ≤ 1 / 2 ^ 60) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits))
      (mainTail u c (kOf u)).toBits := by
  obtain ⟨f, k, hu', K, heq, hff, hf1, hf2, hvu, hhu1, hhu2, hvz, hk0, hkK, hK1, hK2, hK0⟩ :=
    main_reduce u c hu hpos hfar
  obtain ⟨hkd, hA⟩ := kd_exact k K (by omega) (by omega) hkK
  rw [heq, log_split (value x.toBits) (value u.toBits) (value f.toBits)
    ((1 + value x.toBits - value u.toBits) / value u.toBits) K hvu (by linarith)
    (lt_of_lt_of_le (by positivity) hpos) rfl hdom]
  exact tail_main f c k hu' K _ et hff hf1 hf2 hhu1 hhu2 hvz hk0 hkd hA (K_cases K hK1 hK2 hK0)
    hc ht het

/-- The main path from `2 ^ 53` on: `u = x`, `c = 0`, and `K ≥ 53`. -/
theorem big_finish (x : Float) (hx : Finite x.toBits) (h53 : 2 ^ 53 ≤ value x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits))
      (mainTail x 0.0 (kOf x)).toBits := by
  have hpos : (1 : ℝ) / 2 ^ 60 ≤ value x.toBits := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 2 ^ 53)]
  obtain ⟨f, k, hu', K, heq, hff, hf1, hf2, hvu, hhu1, hhu2, hvz, hk0, hkK, hK1, hK2, hK0⟩ :=
    main_reduce x 0.0 hx hpos (Or.inr (by linarith [(by norm_num : (14142132 : ℝ) / 10 ^ 7 ≤ 2 ^ 53)]))
  obtain ⟨hkd, hA⟩ := kd_exact k K (by omega) (by omega) hkK
  have hK53 : 53 ≤ K := by
    by_contra hc
    have hK52 : K ≤ 52 := by omega
    have h1 : (2 : ℝ) ^ K ≤ 2 ^ (52 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hK52
    have h2 : value x.toBits ≤ 2 ^ (52 : ℤ) * (1 + 41422 / 100000) := by
      rw [hvu]
      exact mul_le_mul h1 (by linarith) (by linarith) (by positivity)
    norm_num at h2 h53
    linarith
  have hv0 : 0 < value x.toBits := by linarith [(by norm_num : (0 : ℝ) < 2 ^ 53)]
  have ht : (1 + value x.toBits - value x.toBits) / value x.toBits = 1 / value x.toBits := by ring
  have htb : |1 / value x.toBits| ≤ 1 / 2 ^ 53 := by
    rw [abs_of_pos (one_div_pos.mpr hv0)]
    exact one_div_le_one_div_of_le (by positivity) h53
  have hc : FApprox (0.0 : Float) (1 / value x.toBits) (1 / value x.toBits) := by
    unfold FApprox
    refine ⟨by rw [show (0.0 : Float).toBits = 0 from rfl]; unfold CodeLib.IEEE64.Finite; decide,
      ?_⟩
    rw [zero_bits_value, zero_sub, abs_neg, abs_of_pos (one_div_pos.mpr hv0)]
  rw [heq, log_split (value x.toBits) (value x.toBits) (value f.toBits)
    ((1 + value x.toBits - value x.toBits) / value x.toBits) K hvu (by linarith) hv0 rfl
    (by linarith), ht]
  have hK53' : (50 : ℝ) ≤ K := by exact_mod_cast (show (50 : ℤ) ≤ K by omega)
  have hK2' : (K : ℝ) ≤ 1100 := by exact_mod_cast (show K ≤ 1100 by omega)
  exact tail_big f 0.0 k hu' K _ _ hff hf1 hf2 hhu1 hhu2 hvz hk0 hkd hA hK53' hK2' hc htb
    ((le_abs_self _).trans (htb.trans (by norm_num)))

theorem word_value (w : UInt64) (q : ℚ) (h : PolyBound.ratOfWord w = q) : value w = (q : ℝ) := by
  rw [← PolyBound.ratOfWord_cast, h]

/-- `x = 1 - 2 ^ -53`: `1 + x` rounds to 2, the correction is 0 against `t = -2 ^ -54`, and
`f = 0`. -/
theorem special_two (x : Float) (hxb : x.toBits = 0x3FEFFFFFFFFFFFFF) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits))
      (mainTail (1.0 + x) (cOf x (1.0 + x) / (1.0 + x)) (kOf (1.0 + x))).toBits := by
  have hone : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have hvx : value x.toBits = 1 - 1 / 2 ^ 53 := by
    rw [hxb, word_value _ (1 - 1 / 2 ^ 53) (by decide +kernel)]
    norm_num
  have hu : (1.0 + x).toBits = 0x4000000000000000 := by
    rw [F64Bits.toBits_add, hxb, hone]
    decide +kernel
  have hvu : value (1.0 + x).toBits = 2 := by
    rw [hu, word_value _ 2 (by decide +kernel)]
    norm_num
  have huf : Finite (1.0 + x).toBits := by
    rw [hu]; unfold CodeLib.IEEE64.Finite; decide +kernel
  have hcb : (cOf x (1.0 + x) / (1.0 + x)).toBits = 0 := by
    have hk : kOf (1.0 + x) = 1 := by
      unfold kOf
      rw [hu]
      decide
    unfold cOf
    rw [hk, if_pos (by decide), F64Bits.toBits_div, F64Bits.toBits_sub, F64Bits.toBits_sub, hu,
      hxb, hone]
    decide +kernel
  have hc : FApprox (cOf x (1.0 + x) / (1.0 + x))
      ((1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits) (1 / 2 ^ 54) := by
    unfold FApprox
    rw [hcb, hvx, hvu]
    refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
    rw [F64Magnitude.value_zero]
    norm_num
  obtain ⟨f, k, hu', K, heq, hff, hf1, hf2, hvu', hhu1, hhu2, hvz, hk0, hkK, hK1, hK2, hK0⟩ :=
    main_reduce (1.0 + x) (cOf x (1.0 + x) / (1.0 + x)) huf (by rw [hvu]; norm_num)
      (Or.inr (by rw [hvu]; norm_num))
  obtain ⟨hkd, hA⟩ := kd_exact k K (by omega) (by omega) hkK
  have hK : K = 1 := by
    rw [hvu] at hvu'
    rcases (by omega : K ≤ 0 ∨ K = 1 ∨ 2 ≤ K) with h | h | h
    · have h1 : (2 : ℝ) ^ K ≤ 2 ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) h
      rw [zpow_zero] at h1
      nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 1 + value f.toBits)]
    · exact h
    · have h1 : (2 : ℝ) ^ (2 : ℤ) ≤ 2 ^ K := zpow_le_zpow_right₀ (by norm_num) h
      rw [show (2 : ℝ) ^ (2 : ℤ) = 4 by norm_num] at h1
      nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ 1 + value f.toBits)]
  have hf0 : value f.toBits = 0 := by
    rw [hvu, hK] at hvu'
    norm_num at hvu'
    linarith
  have hhu0 : (hu' == 0) = true := by
    cases h : (hu' == 0)
    · have := hhu1 h
      rw [hf0, abs_zero] at this
      norm_num at this
    · rfl
  have hz : (f == 0.0) = true := (beq_zero_iff f hff).mpr hf0
  rw [heq, Log1pTheoremBranches.tail_z_eq f _ k hu' hk0 hhu0 hz,
    log_split (value x.toBits) (value (1.0 + x).toBits) (value f.toBits)
      ((1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits) K hvu'
      (by linarith) (by rw [hvu]; norm_num) rfl (by rw [hvx]; norm_num)]
  have ht : (1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits =
      -1 / 2 ^ 54 := by
    rw [hvx, hvu]
    norm_num
  rw [ht] at hc ⊢
  rw [hK] at hkd hA ⊢
  refine finish_z _ k (value f.toBits) ((1 : ℤ) : ℝ) (-1 / 2 ^ 54) (1 / 2 ^ 54) 1 1 (1 / 2 ^ 54)
    ((101 / 100) / 2 ^ 54) 1022 hf0 hkd hA (by norm_num) (by norm_num) (by norm_num) hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
  norm_num

/-- **`log1p` within one step.**  For every finite `x > -1`, `Log1p.log1p x` lies within one
representable step of the nearest-even reference of `log (1 + x)`. -/
theorem log1p_within_one (x : Float) (hx : Finite x.toBits) (hdom : -1 < value x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.log (1 + value x.toBits)) (Log1p.log1p x).toBits := by
  have hN := x.toBits.toNat_lt
  have hfin : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x7ff00000 := by
    rw [← ax_toNat]
    exact F64UpperWord.finite_high x.toBits hx
  obtain ⟨hsn, hsp⟩ := sign_value x hx
  have T29 := ax_lt x 0x3e200000 (by norm_num) (1 / 2 ^ 29) (by decide +kernel)
  have TK := ax_lt x 0x3fd2bec5 (by norm_num) (1228485 / 4194304) (by decide +kernel)
  have TP := ax_lt x 0x3FDA827A (by norm_num) (868669 / 2097152) (by decide +kernel)
  have T1 := ax_lt x 0x3ff00000 (by norm_num) 1 (by decide +kernel)
  have T53 := ax_lt x 0x43400000 (by norm_num) (2 ^ 53) (by decide +kernel)
  rw [ax_toNat] at T29 TK TP T1 T53
  push_cast at T29 TK TP T1 T53
  rcases Nat.lt_or_ge x.toBits.toNat (2 ^ 63) with hpos | hneg
  · have hv0 := hsp hpos
    rw [abs_of_nonneg hv0] at T29 TK TP T1 T53
    by_cases c1 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x3e200000
    · exact branch_tiny x hx (by bits_omega) (by rw [ax_toNat]; exact c1)
    have h29 : 1 / 2 ^ 29 ≤ value x.toBits := not_lt.mp (fun h => c1 (T29.mpr h))
    by_cases c2 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x3FDA827A
    · have hP := TP.mp c2
      rw [log1p_k0_eq x (by bits_omega) (by rw [UInt64.lt_iff_toNat_lt, ax_toNat]; simpa using c1)
        (by simp only [ge_iff_le, not_le, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ax_toNat,
              UInt64.reduceToNat, Nat.reducePow] at *
            omega) (by bits_omega),
        tail_k0_eq x 0.0 1 (by decide)]
      by_cases c3 : value x.toBits ≤ 285 / 1000
      · exact k0_pos_low x hx (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 30 ≤ 1 / 2 ^ 29)]) c3
      · exact k0_pos_high x hx (by linarith) (by norm_num at hP ⊢; linarith)
    have hP : 868669 / 2097152 ≤ value x.toBits := not_lt.mp (fun h => c2 (TP.mpr h))
    by_cases c3 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x43400000
    · have h53 := T53.mp c3
      rw [log1p_main_eq x (by bits_omega) (by bits_omega) (by bits_omega) (by bits_omega)
        (by bits_omega)]
      rcases lt_trichotomy x.toBits.toNat 0x3FEFFFFFFFFFFFFF with c4 | c4 | c4
      · have hw : value x.toBits ≤ value (0x3FEFFFFFFFFFFFFE : UInt64) :=
          (F64PositiveOrder.value_le_iff hpos (by decide)).mpr (by
            change x.toBits.toNat ≤ 0x3FEFFFFFFFFFFFFE
            omega)
        rw [word_value (0x3FEFFFFFFFFFFFFE : UInt64) (1 - 1 / 2 ^ 52) (by decide +kernel)] at hw
        push_cast at hw
        obtain ⟨huf, hlo, hlt, hc, ht⟩ := corr_hi x hx (by norm_num at hP ⊢; linarith) hw
        exact main_finish x (1.0 + x) _ hdom huf (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1)])
          (Or.inr hlo) _ hc ht le_rfl
      · have hxb : x.toBits = 0x3FEFFFFFFFFFFFFF := UInt64.toNat_inj.mp c4
        exact special_two x hxb
      · have hw : value (0x3FF0000000000000 : UInt64) ≤ value x.toBits :=
          (F64PositiveOrder.value_le_iff (by decide) hpos).mpr (by
            change 0x3FF0000000000000 ≤ x.toBits.toNat
            omega)
        rw [word_value (0x3FF0000000000000 : UInt64) 1 (by decide +kernel)] at hw
        push_cast at hw
        obtain ⟨huf, hlo, hhi, hc, ht⟩ := corr_big x hx hw h53
        exact main_finish x (1.0 + x) _ hdom huf (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 2)])
          (Or.inr (by linarith)) _ hc ht le_rfl
    · have h53 : 2 ^ 53 ≤ value x.toBits := not_lt.mp (fun h => c3 (T53.mpr h))
      rw [log1p_big_eq x (by bits_omega) (by bits_omega) (by bits_omega) (by bits_omega)
        (by bits_omega)]
      exact big_finish x hx h53
  · have hv0 := hsn hneg
    rw [abs_of_nonpos hv0] at T29 TK TP T1 T53
    by_cases c1 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x3e200000
    · exact branch_tiny x hx (by bits_omega) (by rw [ax_toNat]; exact c1)
    have h29 : 1 / 2 ^ 29 ≤ -value x.toBits := not_lt.mp (fun h => c1 (T29.mpr h))
    by_cases c4 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x3ff00000
    swap
    · exfalso
      have := not_lt.mp (fun h => c4 (T1.mpr h))
      linarith
    by_cases c5 : x.toBits.toNat % 2 ^ 63 / 2 ^ 32 < 0x3fd2bec5
    · have hK := TK.mp c5
      rw [log1p_k0_eq x (by bits_omega) (by rw [UInt64.lt_iff_toNat_lt, ax_toNat]; simpa using c1)
        (by simp only [ge_iff_le, not_le, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, ax_toNat,
              UInt64.reduceToNat, Nat.reducePow] at *
            omega) (by bits_omega),
        tail_k0_eq x 0.0 1 (by decide)]
      exact k0_neg x hx (by norm_num at hK ⊢; linarith)
        (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 30 ≤ 1 / 2 ^ 29)])
    have hK : 1228485 / 4194304 ≤ -value x.toBits := not_lt.mp (fun h => c5 (TK.mpr h))
    rw [log1p_main_eq x (by bits_omega) (by bits_omega) (by bits_omega) (by bits_omega)
      (by bits_omega)]
    by_cases c6 : value x.toBits ≤ -1 / 2
    · obtain ⟨huf, hvu, hgrid, hc⟩ := corr_low x hx hdom c6
      refine main_finish x (1.0 + x) _ hdom huf
        (le_trans (by norm_num) hgrid) (Or.inl (by rw [hvu]; linarith)) _ hc ?_ (by norm_num)
      rw [hvu, show 1 + value x.toBits - (1 + value x.toBits) = 0 by ring, zero_div, abs_zero]
      positivity
    · obtain ⟨huf, hlo, hhi, hc, ht⟩ := corr_mid x hx (by linarith) (by linarith)
      exact main_finish x (1.0 + x) _ hdom huf (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1 / 2)])
        (Or.inl hhi) _ hc ht le_rfl

#print axioms log1p_within_one

end Verified.Examples.Log1pTheorem
