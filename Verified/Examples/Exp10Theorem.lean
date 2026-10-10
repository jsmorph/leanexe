import Verified.Examples.Exp10Paths
import Verified.Examples.Exp2Theorem

/-!
The accuracy theorem for `Exp2.exp10`.  For every finite binary64 input `a`, the result lies
within one representable step of the nearest-even rounding of the real `10 ^ a`, overflow to
positive infinity from `0x1.34413509f79ffp8` on and underflow to zero below -350 included.  The
exceptional inputs give `exp10 (±0) = 1`, `exp10 (+∞) = +∞`, `exp10 (-∞) = +0`, and the
canonical NaN for a NaN.
-/

namespace Verified.Examples.Exp10Theorem
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude ExpBranches F64ExponentBounds Exp10Constants

set_option exponentiation.threshold 4096

private theorem sub_guard (a : UInt64) (hlo : 966 ≤ a.toNat) :
    (a - 966).toNat = a.toNat - 966 :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)

theorem tiny_selected (tab : Array UInt64) (x : Float)
    (hx : Wasm.IEEE64.exponent x.toBits < 966) :
    Exp2.exp10With tab x = x + 1.0 := by
  have hs : (exponentWord x.toBits - 966).toNat = 2 ^ 64 - 966 + Wasm.IEEE64.exponent x.toBits := by
    rw [UInt64.toNat_sub, exponent_word_spec]
    change (2 ^ 64 - 966 + Wasm.IEEE64.exponent x.toBits) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hg1 : exponentWord x.toBits - 966 ≥ (0x41 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hs]
    change 0x41 ≤ _
    omega
  have hg2 : exponentWord x.toBits - 966 ≥ (0x80000000 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hs]
    change 0x80000000 ≤ _
    omega
  simp only [Exp2.exp10With, exponentWord] at hg1 hg2 ⊢
  rw [ite_eq_left hg1, ite_eq_left hg2]

theorem ordinary_selected (tab : Array UInt64) (x : Float)
    (hlo : 966 ≤ Wasm.IEEE64.exponent x.toBits) (hhi : Wasm.IEEE64.exponent x.toBits < 1031) :
    Exp2.exp10With tab x = Exp2.exp10Core tab x false := by
  have hw := exponent_word_spec x.toBits
  have hg : ¬ exponentWord x.toBits - 966 ≥ (0x41 : UInt64) := by
    intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [sub_guard _ (by omega)] at hn
    change 0x41 ≤ _ at hn
    omega
  simp only [Exp2.exp10With, exponentWord] at hg ⊢
  rw [ite_eq_right hg]

theorem big_guards (x : UInt64) (he : 1031 ≤ Wasm.IEEE64.exponent x) :
    exponentWord x - 966 ≥ (0x41 : UInt64) ∧ ¬ exponentWord x - 966 ≥ (0x80000000 : UInt64) := by
  have hw := exponent_word_spec x
  have hlt := Nat.mod_lt (x.toNat / 2 ^ 52) (show 0 < 2 ^ 11 by norm_num)
  change Wasm.IEEE64.exponent x < 2 ^ 11 at hlt
  refine ⟨?_, ?_⟩
  · apply UInt64.le_iff_toNat_le.mpr
    rw [sub_guard _ (by omega)]
    change 0x41 ≤ _
    omega
  · intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [sub_guard _ (by omega)] at hn
    change 0x80000000 ≤ _ at hn
    omega

theorem not_top (x : UInt64) (hf : Wasm.IEEE64.exponent x < 2047) :
    ¬ (exponentWord x == 0x7ff) = true := by
  have hw := exponent_word_spec x
  intro h
  have := congrArg UInt64.toNat (beq_iff_eq.mp h)
  rw [hw] at this
  change Wasm.IEEE64.exponent x = 2047 at this
  omega

theorem overflow_selected (tab : Array UInt64) (x : Float)
    (he : 1031 ≤ Wasm.IEEE64.exponent x.toBits) (hf : Wasm.IEEE64.exponent x.toBits < 2047)
    (ho : x ≥ Float.ofBits 0x40734413509F79FF) :
    Exp2.exp10With tab x = Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000 := by
  obtain ⟨hg1, hg2⟩ := big_guards x.toBits he
  have hg3 := not_top x.toBits hf
  simp only [Exp2.exp10With, exponentWord] at hg1 hg2 hg3 ⊢
  simp only [hg1, hg2, hg3, ho, ite_true, ite_false, Bool.false_eq_true]

theorem underflow_selected (tab : Array UInt64) (x : Float)
    (he : 1031 ≤ Wasm.IEEE64.exponent x.toBits) (hf : Wasm.IEEE64.exponent x.toBits < 2047)
    (ho : ¬ x ≥ Float.ofBits 0x40734413509F79FF) (hu : x < Float.ofBits 0xC075E00000000000) :
    Exp2.exp10With tab x = Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000 := by
  obtain ⟨hg1, hg2⟩ := big_guards x.toBits he
  have hg3 := not_top x.toBits hf
  simp only [Exp2.exp10With, exponentWord] at hg1 hg2 hg3 ⊢
  simp only [hg1, hg2, hg3, ho, hu, ite_true, ite_false, Bool.false_eq_true]

theorem core_selected (tab : Array UInt64) (x : Float)
    (he : 1031 ≤ Wasm.IEEE64.exponent x.toBits) (hf : Wasm.IEEE64.exponent x.toBits < 2047)
    (ho : ¬ x ≥ Float.ofBits 0x40734413509F79FF) (hu : ¬ x < Float.ofBits 0xC075E00000000000) :
    Exp2.exp10With tab x = Exp2.exp10Core tab x true := by
  obtain ⟨hg1, hg2⟩ := big_guards x.toBits he
  have hg3 := not_top x.toBits hf
  simp only [Exp2.exp10With, exponentWord] at hg1 hg2 hg3 ⊢
  simp only [hg1, hg2, hg3, ho, hu, ite_true, ite_false, Bool.false_eq_true]

theorem nonfinite_selected (tab : Array UInt64) (x : Float)
    (he : Wasm.IEEE64.exponent x.toBits = 2047) :
    Exp2.exp10With tab x = if x.toBits == 0xFFF0000000000000 then 0.0 else x + 1.0 := by
  have hw := exponent_word_spec x.toBits
  obtain ⟨hg1, hg2⟩ := big_guards x.toBits (by omega)
  have hg3 : (exponentWord x.toBits == 0x7ff) = true := by
    apply beq_iff_eq.mpr
    apply UInt64.toNat_inj.mp
    rw [hw, he]
    rfl
  simp only [Exp2.exp10With, exponentWord] at hg1 hg2 hg3 ⊢
  simp only [hg1, hg2, hg3, ite_true, ite_false]

/-- Comparisons of finite floats are comparisons of their values. -/
theorem le_iff_value (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a ≤ b ↔ value a.toBits ≤ value b.toBits := by
  rw [F64Bits.le_iff]
  simp only [Wasm.IEEE64.le, not_nan_of_finite ha, not_nan_of_finite hb, Bool.or_false,
    Bool.false_eq_true, ite_false, decide_eq_true_eq, value]
  rw [div_le_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem lt_iff_value (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a < b ↔ value a.toBits < value b.toBits := by
  rw [F64Bits.lt_iff]
  simp only [Wasm.IEEE64.lt, not_nan_of_finite ha, not_nan_of_finite hb, Bool.or_false,
    Bool.false_eq_true, ite_false, decide_eq_true_eq, value]
  rw [div_lt_div_iff_of_pos_right (by positivity)]
  exact_mod_cast Iff.rfl

theorem bound_words :
    (Float.ofBits 0x40734413509F79FF).toBits = oflowWord ∧
      (Float.ofBits 0xC075E00000000000).toBits = 0xC075E00000000000 ∧
      Finite oflowWord ∧ Finite (0xC075E00000000000 : UInt64) ∧
      value (0xC075E00000000000 : UInt64) = -350 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [F64Bits.toBits_ofBits]
    decide +kernel
  · rw [F64Bits.toBits_ofBits]
    decide +kernel
  · unfold CodeLib.IEEE64.Finite oflowWord
    decide +kernel
  · unfold CodeLib.IEEE64.Finite
    decide +kernel
  · have h : Wasm.IEEE64.scaledValue (0xC075E00000000000 : UInt64) = -350 * (2 : Int) ^ 1074 := by
      decide +kernel
    rw [value, h, Int.cast_mul, Int.cast_pow]
    norm_num

/-- `x + 1` for `|x| ≤ 2 ^ -57`. -/
theorem tiny_within (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 1 / 2 ^ 57) :
    F64SignedRounding.WithinSteps 1 ((10 : ℝ) ^ value x) (Wasm.IEEE64.add x 0x3FF0000000000000) := by
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  have h10 : (10 : ℝ) ^ value x = Real.exp (value x * Real.log 10) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  rw [h10]
  have hone := ExpTinyError.one_value
  have honef : Finite (0x3FF0000000000000 : UInt64) := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  rw [Exp10Core.add_comm_finite _ _ hxf honef]
  have hxb := abs_le.mp hx
  have hsum : |value 0x3FF0000000000000 + value x| < (2 : ℝ) ^ 1023 := by
    rw [hone, abs_lt]
    constructor <;> linarith [show (1 : ℝ) / 2 ^ 57 ≤ 1 by norm_num,
      show (2 : ℝ) < 2 ^ 1023 by norm_num]
  obtain ⟨hrf, hre⟩ := F64AddBounds.add_real_relative _ x honef hxf hsum
  rw [hone] at hre
  obtain ⟨hl, hh⟩ := log_ten_enclosure
  have hb := checked_reduction
  have hl' : (23 / 10 : ℝ) ≤ Real.log 10 := le_trans (by
    have := Exp2Approximation.cast_le hb.2.2.2.2.2.1
    push_cast at this
    exact this) hl
  have hh' : Real.log 10 ≤ 233 / 100 := hh.trans (by
    have := Exp2Approximation.cast_le hb.2.2.2.2.2.2.1
    push_cast at this
    exact this)
  have hy : |value x * Real.log 10| ≤ 1 / 2 ^ 55 := by
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < Real.log 10 by linarith)]
    calc
      _ ≤ 1 / 2 ^ 57 * (233 / 100) := mul_le_mul hx hh' (by linarith) (by positivity)
      _ ≤ 1 / 2 ^ 55 := by norm_num
  have hb2 := Real.exp_bound (x := value x * Real.log 10) (hy.trans (by norm_num)) (n := 2)
    (by norm_num)
  have hs : ∑ i ∈ Finset.range 2, (value x * Real.log 10) ^ i / (i.factorial : ℝ) =
      1 + value x * Real.log 10 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, pow_zero, pow_one,
      Nat.cast_one, div_one, zero_add, Nat.succ_eq_add_one, Nat.cast_mul]
    ring
  rw [hs] at hb2
  have hy2 : |value x * Real.log 10| ^ 2 ≤ (1 / 2 ^ 55) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) hy 2
  have hc : |value x * Real.log 10| ^ 2 *
      ((Nat.succ 2 : Nat) / ((Nat.factorial 2 : Nat) * (2 : Nat)) : ℝ) ≤ (1 / 2 ^ 55) ^ 2 * 1 :=
    mul_le_mul hy2 (by norm_num [Nat.factorial]) (by positivity) (by positivity)
  have hb' := abs_le.mp hb2
  have hlin : |value x * Real.log 10 - value x| ≤ 1 / 2 ^ 57 * (4 / 3) := by
    rw [show value x * Real.log 10 - value x = value x * (Real.log 10 - 1) by ring, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ Real.log 10 - 1 by linarith)]
    exact mul_le_mul hx (by linarith) (by linarith) (by positivity)
  have hlin' := abs_le.mp hlin
  have hpos : 1 - 1 / 2 ^ 55 ≤ Real.exp (value x * Real.log 10) := by
    have := Real.add_one_le_exp (value x * Real.log 10)
    have := (abs_le.mp hy).1
    linarith
  have h1x : |1 + value x| ≤ 1 + 1 / 2 ^ 57 := by
    rw [abs_le]
    constructor <;> linarith [show (1 : ℝ) / 2 ^ 57 ≤ 1 by norm_num]
  have hre' : |value (Wasm.IEEE64.add 0x3FF0000000000000 x) - (1 + value x)| ≤
      1 / 2 ^ 53 * (1 + 1 / 2 ^ 57) := by
    rw [hu] at hre
    exact hre.trans (mul_le_mul_of_nonneg_left h1x (by positivity))
  have hre'' := abs_le.mp hre'
  apply F64RelativeStep.within_one_relative _ _ hrf
  · rw [abs_of_pos (Real.exp_pos _)]
    have : (1 : ℝ) / 2 ^ 1000 ≤ 1 - 1 / 2 ^ 55 := by norm_num
    linarith
  · rw [abs_of_pos (Real.exp_pos _), hu]
    have hnum : (1 : ℝ) / 2 ^ 53 * (1 + 1 / 2 ^ 57) + 1 / 2 ^ 57 * (4 / 3) +
        (1 / 2 ^ 55) ^ 2 * 1 ≤ 11 / 8 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 55) := by norm_num
    have hmono : 11 / 8 * (1 / 2 ^ 53) * (1 - 1 / 2 ^ 55) ≤
        11 / 8 * (1 / 2 ^ 53) * Real.exp (value x * Real.log 10) :=
      mul_le_mul_of_nonneg_left hpos (by positivity)
    rw [abs_le]
    constructor <;> linarith

theorem exp10_le (a b : ℝ) (h : a ≤ b) : (10 : ℝ) ^ a ≤ 10 ^ b :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- The accuracy theorem: `Exp2.exp10` is within one step of the nearest-even rounding of
`10 ^ a` for every finite input `a`. -/
theorem exp10_within (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 ((10 : ℝ) ^ value x.toBits) (Exp2.exp10 x).toBits := by
  have hf : Wasm.IEEE64.exponent x.toBits < 2047 := by
    have h := hxf
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, bne_iff_ne, ne_eq] at h
    have : Wasm.IEEE64.exponent x.toBits < 2048 := Nat.mod_lt _ (by norm_num)
    omega
  obtain ⟨ho1, hu1, hof, huf, huv⟩ := bound_words
  rw [Exp2.exp10]
  rcases (show Wasm.IEEE64.exponent x.toBits < 966 ∨
      (966 ≤ Wasm.IEEE64.exponent x.toBits ∧ Wasm.IEEE64.exponent x.toBits < 1031) ∨
      1031 ≤ Wasm.IEEE64.exponent x.toBits by omega) with he | ⟨he1, he2⟩ | he
  · have hx : |value x.toBits| ≤ 1 / 2 ^ 57 := by
      have h := magnitude_le_boundary x.toBits 966 (by decide) he
      have hb : value (boundary 966) = 1 / (2 : ℝ) ^ 57 := by
        have h := F64NearestBinade.boundary_power 966 (-57) (by decide) (by decide) (by decide)
        have hp : (2 : ℝ) ^ (-57 : Int) = 1 / (2 : ℝ) ^ 57 := by norm_num
        exact h.trans hp
      rwa [hb, abs_of_pos (by positivity : (0 : ℝ) < 1 / 2 ^ 57)] at h
    rw [tiny_selected _ x he, F64Bits.toBits_add]
    have h1 : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
    rw [h1]
    exact tiny_within _ hxf hx
  · have hx := magnitude_lt x.toBits 1031 8 (by norm_num) (by norm_num) he2
    rw [ordinary_selected _ x he1 he2]
    exact Exp10Paths.ordinary_within x hxf (by norm_num at hx; exact hx)
  · have hge := magnitude_ge x.toBits 1031 8 (by norm_num) (by norm_num) (by norm_num) he
    norm_num at hge
    by_cases ho : x ≥ Float.ofBits 0x40734413509F79FF
    · rw [overflow_selected _ x he hf ho, ExpTheorem.overflow_product]
      have hv := (le_iff_value _ _ (by rw [ho1]; exact hof) hxf).mp ho
      rw [ho1] at hv
      apply Exp2Theorem.overflow_within
      -- `x log 10 ≥ 1024 log 2`
      obtain ⟨hl, -⟩ := log_ten_enclosure
      obtain ⟨-, hh2⟩ := ExpReductionBounds.log_two_enclosure
      have hb := checked_reduction
      have hp := Exp2Approximation.cast_le hb.2.2.2.2.2.2.2.1
      push_cast at hp
      rw [PolyBound.ratOfWord_cast] at hp
      have hpos : 0 ≤ value oflowWord := by
        have hs : Wasm.IEEE64.scaledValue oflowWord = 5422874305198591 * 2 ^ 1030 := by
          unfold oflowWord
          decide +kernel
        rw [value, hs]
        positivity
      have hL10 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
      have h1 : 1024 * Real.log 2 ≤ value x.toBits * Real.log 10 := by
        have := mul_le_mul_of_nonneg_left hl hpos
        have := mul_le_mul_of_nonneg_right hv hL10
        linarith
      have h2 : Real.exp (1024 * Real.log 2) = 2 ^ 1024 := by
        have := RealExpError.exp_pow_two 1024
        push_cast at this
        exact this
      rw [Real.rpow_def_of_pos (by norm_num), mul_comm, ← h2]
      exact Real.exp_le_exp.mpr h1
    · by_cases hu : x < Float.ofBits 0xC075E00000000000
      · rw [underflow_selected _ x he hf ho hu, ExpTheorem.underflow_product]
        have hv := (lt_iff_value _ _ hxf (by rw [hu1]; exact huf)).mp hu
        rw [hu1, huv] at hv
        apply Exp2Theorem.zero_within _ (Real.rpow_pos_of_pos (by norm_num) _)
        obtain ⟨hl, -⟩ := log_ten_enclosure
        obtain ⟨-, hh2⟩ := ExpReductionBounds.log_two_enclosure
        have hb := checked_reduction
        have hp := Exp2Approximation.cast_le hb.2.2.2.2.2.2.2.2.2
        push_cast at hp
        have hL10 : 0 ≤ Real.log 10 := Real.log_nonneg (by norm_num)
        have h1 : value x.toBits * Real.log 10 ≤ -1075 * Real.log 2 := by
          have := mul_le_mul_of_nonneg_right hv.le hL10
          linarith
        have h2 : Real.exp (-1075 * Real.log 2) = 1 / 2 ^ 1075 := by
          have := RealExpError.exp_pow_two 1075
          push_cast at this
          rw [neg_mul, Real.exp_neg, this, inv_eq_one_div]
        rw [Real.rpow_def_of_pos (by norm_num), mul_comm, ← h2]
        exact Real.exp_le_exp.mpr h1
      · rw [core_selected _ x he hf ho hu]
        have hvo : value x.toBits < value oflowWord := by
          have h := (le_iff_value _ _ (by rw [ho1]; exact hof) hxf).not.mp ho
          rw [ho1] at h
          exact lt_of_not_ge h
        have hvu : -350 ≤ value x.toBits := by
          have h := (lt_iff_value _ _ hxf (by rw [hu1]; exact huf)).not.mp hu
          rw [hu1, huv] at h
          exact le_of_not_gt h
        rcases le_or_gt 0 (value x.toBits) with hpos | hneg
        · rw [abs_of_nonneg hpos] at hge
          -- the double below the overflow bound
          have hxs : x.toBits.toNat < 2 ^ 63 := by
            by_contra hn
            have hs : Wasm.IEEE64.sign x.toBits = true := by
              simp only [Wasm.IEEE64.sign]
              exact decide_eq_true (by omega)
            have hmag : 0 < Wasm.IEEE64.scaledMagnitude x.toBits := by
              simp only [Wasm.IEEE64.scaledMagnitude, beq_iff_eq,
                show Wasm.IEEE64.exponent x.toBits ≠ 0 by omega, ite_false]
              positivity
            have := (sign_value _ hmag).mp hs
            linarith
          have hon : (oflowWord : UInt64).toNat < 2 ^ 63 := by decide
          have hlt : x.toBits.toNat < oflowWord.toNat := by
            by_contra hn
            have := (F64PositiveOrder.value_le_iff hon hxs).mpr (by omega)
            linarith
          have hbw : x.toBits.toNat ≤ belowOflowWord.toNat := by
            have : oflowWord.toNat = belowOflowWord.toNat + 1 := by decide
            omega
          have hbv := (F64PositiveOrder.value_le_iff hxs (by decide)).mpr hbw
          exact Exp10Paths.positive_within x hxf hge hbv
        · rw [abs_of_neg hneg] at hge
          exact Exp10Paths.negative_within x hxf hvu (by linarith)

theorem exp10_pos_infinity :
    (Exp2.exp10 (Float.ofBits 0x7FF0000000000000)).toBits = 0x7FF0000000000000 := by
  have hb : (Float.ofBits 0x7FF0000000000000).toBits = 0x7FF0000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp2.exp10, nonfinite_selected _ _ (by rw [hb]; decide +kernel), hb,
    ite_eq_right (by decide), F64Bits.toBits_add, hb]
  decide +kernel

theorem exp10_neg_infinity : (Exp2.exp10 (Float.ofBits 0xFFF0000000000000)).toBits = 0 := by
  have hb : (Float.ofBits 0xFFF0000000000000).toBits = 0xFFF0000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp2.exp10, nonfinite_selected _ _ (by rw [hb]; decide +kernel), hb, ite_eq_left (by decide)]
  rfl

theorem exp10_nan (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true) :
    (Exp2.exp10 x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hc := F64Bits.toBits_canonical x
  rw [ite_eq_left h] at hc
  rw [Exp2.exp10, nonfinite_selected _ _ (by rw [← hc]; decide +kernel), ← hc,
    ite_eq_right (by decide), F64Bits.toBits_add, ← hc]
  decide +kernel

theorem exp10_pos_zero : (Exp2.exp10 (Float.ofBits 0)).toBits = 0x3FF0000000000000 := by
  have hb : (Float.ofBits 0).toBits = 0 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp2.exp10, tiny_selected _ _ (by rw [hb]; decide +kernel), F64Bits.toBits_add, hb]
  decide +kernel

theorem exp10_neg_zero :
    (Exp2.exp10 (Float.ofBits 0x8000000000000000)).toBits = 0x3FF0000000000000 := by
  have hb : (Float.ofBits 0x8000000000000000).toBits = 0x8000000000000000 := by
    rw [F64Bits.toBits_ofBits]
    decide +kernel
  rw [Exp2.exp10, tiny_selected _ _ (by rw [hb]; decide +kernel), F64Bits.toBits_add, hb]
  decide +kernel

#print axioms tiny_selected
#print axioms ordinary_selected
#print axioms overflow_selected
#print axioms underflow_selected
#print axioms core_selected
#print axioms nonfinite_selected
#print axioms le_iff_value
#print axioms lt_iff_value
#print axioms tiny_within
#print axioms exp10_within
#print axioms exp10_pos_infinity
#print axioms exp10_neg_infinity
#print axioms exp10_nan
#print axioms exp10_pos_zero
#print axioms exp10_neg_zero

end Verified.Examples.Exp10Theorem
