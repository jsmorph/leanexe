import Library.Numerics.Float64.Exp2.Exp2Paths
import Library.Numerics.Float64.Exp.ExpTheorem

/-!
The branches of `Exp2.exp2With`.  The exponent field `abstop` selects `1 + x` below `2 ^ -54`,
the ordinary reconstruction below 512, `exp2Core` with the special flag `|x| > 928` below 1024,
and from 1024 on the overflow and underflow products, `exp2Core` with the special flag for
`-1075 < x ≤ -1024`, `+0` for `-∞`, and `1 + x` for an infinity or NaN.
-/

namespace Library.Numerics.Float64.Exp2.Exp2Branches
open CodeLib.IEEE64
open LeanExe.ProofKit F64Magnitude Library.Numerics.Float64.Exp.ExpBranches

set_option exponentiation.threshold 4096

private theorem sub_guard (a : UInt64) (hlo : 969 ≤ a.toNat) :
    (a - 969).toNat = a.toNat - 969 :=
  UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr hlo)

theorem tiny_selected (tab : Array UInt64) (x : Float)
    (hx : Wasm.IEEE64.exponent x.toBits < 969) :
    Exp2.exp2With tab x = 1.0 + x := by
  have hs : (exponentWord x.toBits - 969).toNat = 2 ^ 64 - 969 + Wasm.IEEE64.exponent x.toBits := by
    rw [UInt64.toNat_sub, exponent_word_spec]
    change (2 ^ 64 - 969 + Wasm.IEEE64.exponent x.toBits) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hg1 : exponentWord x.toBits - 969 ≥ (63 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hs]
    change 63 ≤ _
    omega
  have hg2 : exponentWord x.toBits - 969 ≥ (0x80000000 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [hs]
    change 0x80000000 ≤ _
    omega
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp2.exp2With, exponentWord, hc] at hg1 hg2 ⊢
  rw [ite_eq_left hg1, ite_eq_left hg2]

theorem ordinary_selected (tab : Array UInt64) (x : Float)
    (hlo : 969 ≤ Wasm.IEEE64.exponent x.toBits) (hhi : Wasm.IEEE64.exponent x.toBits < 1032) :
    Exp2.exp2With tab x = Exp2.exp2Core tab x false := by
  have hw := exponent_word_spec x.toBits
  have hg : ¬ exponentWord x.toBits - 969 ≥ (63 : UInt64) := by
    intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [sub_guard _ (by omega)] at hn
    change 63 ≤ _ at hn
    omega
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp2.exp2With, exponentWord, hc] at hg ⊢
  rw [ite_eq_right hg]

theorem special_selected (tab : Array UInt64) (x : Float)
    (he : Wasm.IEEE64.exponent x.toBits = 1032) :
    Exp2.exp2With tab x =
      Exp2.exp2Core tab x (2 * x.toBits > 2 * 0x408D000000000000) := by
  have hw := exponent_word_spec x.toBits
  have hg1 : exponentWord x.toBits - 969 ≥ (63 : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    rw [sub_guard _ (by omega)]
    change 63 ≤ _
    omega
  have hg2 : ¬ exponentWord x.toBits - 969 ≥ (0x80000000 : UInt64) := by
    intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [sub_guard _ (by omega)] at hn
    change 0x80000000 ≤ _ at hn
    omega
  have hg3 : ¬ exponentWord x.toBits ≥ (0x409 : UInt64) := by
    intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    change 0x409 ≤ _ at hn
    omega
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp2.exp2With, exponentWord, hc] at hg1 hg2 hg3 ⊢
  simp only [hg1, hg2, hg3, ite_true, ite_false, decide_false, Bool.false_and,
    Bool.false_eq_true]

/-- The guards from exponent field 1033 on. -/
theorem big_guards (x : UInt64) (he : 1033 ≤ Wasm.IEEE64.exponent x) :
    exponentWord x - 969 ≥ (63 : UInt64) ∧ ¬ exponentWord x - 969 ≥ (0x80000000 : UInt64) ∧
      exponentWord x ≥ (0x409 : UInt64) := by
  have hw := exponent_word_spec x
  refine ⟨?_, ?_, ?_⟩
  · apply UInt64.le_iff_toNat_le.mpr
    rw [sub_guard _ (by omega)]
    change 63 ≤ _
    omega
  · intro h
    have hn := UInt64.le_iff_toNat_le.mp h
    rw [sub_guard _ (by omega)] at hn
    change 0x80000000 ≤ _ at hn
    have := Nat.mod_lt (x.toNat / 2 ^ 52) (show 0 < 2 ^ 11 by norm_num)
    change Wasm.IEEE64.exponent x < 2 ^ 11 at this
    omega
  · apply UInt64.le_iff_toNat_le.mpr
    change 0x409 ≤ _
    omega

theorem not_neg_infinity (x : UInt64) (hf : Wasm.IEEE64.exponent x < 2047) :
    ¬ (x == 0xFFF0000000000000) = true := by
  intro h
  have heq : x = 0xFFF0000000000000 := by simpa using h
  rw [heq] at hf
  exact absurd hf (by decide)

theorem big_finite_guard (x : UInt64) (hf : Wasm.IEEE64.exponent x < 2047) :
    ¬ exponentWord x ≥ (0x7ff : UInt64) := by
  have hw := exponent_word_spec x
  intro h
  have hn := UInt64.le_iff_toNat_le.mp h
  change 0x7ff ≤ _ at hn
  omega

theorem overflow_selected (tab : Array UInt64) (x : Float)
    (he : 1033 ≤ Wasm.IEEE64.exponent x.toBits) (hf : Wasm.IEEE64.exponent x.toBits < 2047)
    (hs : (x.toBits >>> 63 == 0) = true) :
    Exp2.exp2With tab x = Float.ofBits 0x7000000000000000 * Float.ofBits 0x7000000000000000 := by
  obtain ⟨hg1, hg2, hg3⟩ := big_guards x.toBits he
  have hg4 := big_finite_guard x.toBits hf
  have hninf := not_neg_infinity x.toBits hf
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp2.exp2With, exponentWord, hc] at hg1 hg2 hg3 hg4 ⊢
  simp only [hg1, hg2, hg3, hg4, hninf, hs, ite_true, ite_false, decide_true, decide_false,
    Bool.true_and, Bool.false_eq_true]

theorem underflow_selected (tab : Array UInt64) (x : Float)
    (he : 1033 ≤ Wasm.IEEE64.exponent x.toBits) (hf : Wasm.IEEE64.exponent x.toBits < 2047)
    (hs : ¬ (x.toBits >>> 63 == 0) = true) (hb : x.toBits ≥ 0xC090CC0000000000) :
    Exp2.exp2With tab x = Float.ofBits 0x1000000000000000 * Float.ofBits 0x1000000000000000 := by
  obtain ⟨hg1, hg2, hg3⟩ := big_guards x.toBits he
  have hg4 := big_finite_guard x.toBits hf
  have hninf := not_neg_infinity x.toBits hf
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp2.exp2With, exponentWord, hc] at hg1 hg2 hg3 hg4 ⊢
  simp only [hg1, hg2, hg3, hg4, hninf, hs, hb, ite_true, ite_false, decide_true, decide_false,
    Bool.true_and, Bool.false_eq_true]

theorem big_core_selected (tab : Array UInt64) (x : Float)
    (he : 1033 ≤ Wasm.IEEE64.exponent x.toBits) (hf : Wasm.IEEE64.exponent x.toBits < 2047)
    (hs : ¬ (x.toBits >>> 63 == 0) = true) (hb : ¬ x.toBits ≥ 0xC090CC0000000000)
    (hflag : 2 * x.toBits > 2 * (0x408D000000000000 : UInt64)) :
    Exp2.exp2With tab x = Exp2.exp2Core tab x true := by
  obtain ⟨hg1, hg2, hg3⟩ := big_guards x.toBits he
  have hg4 := big_finite_guard x.toBits hf
  have hninf := not_neg_infinity x.toBits hf
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp2.exp2With, exponentWord, hc] at hg1 hg2 hg3 hg4 ⊢
  simp only [hg1, hg2, hg3, hg4, hninf, hs, hb, hflag, ite_true, ite_false, decide_true,
    decide_false, Bool.true_and, Bool.false_eq_true]

theorem neg_infinity_selected (tab : Array UInt64) (x : Float)
    (h : x.toBits = 0xFFF0000000000000) : Exp2.exp2With tab x = 0.0 := by
  have he : Wasm.IEEE64.exponent x.toBits = 2047 := by rw [h]; decide
  have hw := exponent_word_spec x.toBits
  have hg : exponentWord x.toBits - 969 ≥ (63 : UInt64) ∧
      ¬ exponentWord x.toBits - 969 ≥ (0x80000000 : UInt64) ∧
      exponentWord x.toBits ≥ (0x409 : UInt64) := big_guards x.toBits (by omega)
  obtain ⟨hg1, hg2, hg3⟩ := hg
  have hb : (x.toBits == 0xFFF0000000000000) = true := by rw [h]; rfl
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp2.exp2With, exponentWord, hc] at hg1 hg2 hg3 ⊢
  simp only [hg1, hg2, hg3, hb, ite_true, ite_false, decide_true, Bool.true_and]

theorem nonfinite_selected (tab : Array UInt64) (x : Float)
    (he : Wasm.IEEE64.exponent x.toBits = 2047) (h : x.toBits ≠ 0xFFF0000000000000) :
    Exp2.exp2With tab x = 1.0 + x := by
  have hw := exponent_word_spec x.toBits
  obtain ⟨hg1, hg2, hg3⟩ := big_guards x.toBits (by omega)
  have hg4 : exponentWord x.toBits ≥ (0x7ff : UInt64) := by
    apply UInt64.le_iff_toNat_le.mpr
    change 0x7ff ≤ _
    omega
  have hb : ¬ (x.toBits == 0xFFF0000000000000) = true := by simpa using h
  have hc : (0x408 : UInt64) - 0x3C9 = 63 := by decide
  simp only [Exp2.exp2With, exponentWord, hc] at hg1 hg2 hg3 hg4 ⊢
  simp only [hg1, hg2, hg3, hg4, hb, ite_true, ite_false, decide_true, Bool.true_and,
    Bool.false_eq_true]

/-- The special flag for exponent field 1032: `|x| > 928`. -/
theorem flag_special (x : UInt64) (he : Wasm.IEEE64.exponent x = 1032) :
    decide (2 * x > 2 * (0x408D000000000000 : UInt64)) = decide (928 < |value x|) := by
  have hf : Wasm.IEEE64.fraction x < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hx := x.toNat_lt
  have hmag : Wasm.IEEE64.scaledMagnitude x = (2 ^ 52 + Wasm.IEEE64.fraction x) * 2 ^ 1031 := by
    simp only [Wasm.IEEE64.scaledMagnitude, he, beq_iff_eq, show (1032 : Nat) ≠ 0 by norm_num,
      ite_false]
  have habs : |value x| = ((2 ^ 52 + Wasm.IEEE64.fraction x : Nat) : ℝ) / 2 ^ 43 := by
    rw [value, abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074), ← Int.cast_abs,
      Int.abs_eq_natAbs, Int.cast_natCast, natAbs_scaledValue, hmag, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat, show (2 : ℝ) ^ 1074 = 2 ^ 43 * 2 ^ 1031 by norm_num,
      mul_div_mul_right _ _ (by positivity : (2 : ℝ) ^ 1031 ≠ 0)]
  have hbits : (2 * x > 2 * (0x408D000000000000 : UInt64)) ↔
      0xD000000000000 < Wasm.IEEE64.fraction x := by
    rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
    simp only [UInt64.toNat_mul, UInt64.reduceToNat, Nat.reduceMul]
    have he' : x.toNat / 2 ^ 52 % 2 ^ 11 = 1032 := he
    have hf' : Wasm.IEEE64.fraction x = x.toNat % 2 ^ 52 := rfl
    rw [hf']
    omega
  have hval : (928 < |value x|) ↔ 0xD000000000000 < Wasm.IEEE64.fraction x := by
    rw [habs, lt_div_iff₀ (by positivity)]
    constructor
    · intro h
      have h' : (928 * 2 ^ 43 : ℝ) < ((2 ^ 52 + Wasm.IEEE64.fraction x : Nat) : ℝ) := by
        linarith
      have h'' : 928 * 2 ^ 43 < 2 ^ 52 + Wasm.IEEE64.fraction x := by exact_mod_cast h'
      omega
    · intro h
      have h' : 928 * 2 ^ 43 < 2 ^ 52 + Wasm.IEEE64.fraction x := by omega
      have h'' : (928 * 2 ^ 43 : ℝ) < ((2 ^ 52 + Wasm.IEEE64.fraction x : Nat) : ℝ) := by
        exact_mod_cast h'
      linarith
  exact decide_eq_decide.mpr (hbits.trans hval.symm)

/-- From exponent field 1033 on, the special flag holds. -/
theorem flag_big (x : UInt64) (he : 1033 ≤ Wasm.IEEE64.exponent x) :
    (2 * x > 2 * (0x408D000000000000 : UInt64)) := by
  have hx := x.toNat_lt
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt]
  simp only [UInt64.toNat_mul, UInt64.reduceToNat, Nat.reduceMul]
  have he' : 1033 ≤ x.toNat / 2 ^ 52 % 2 ^ 11 := he
  omega

/-- A double below 1024 is at most `1024 - 2 ^ -43`. -/
theorem below_top (x : UInt64) (hx : value x < 1024) :
    value x ≤ 1024 - 1 / 2 ^ 43 := by
  by_cases h512 : value x < 512
  · linarith [show (0 : ℝ) < 1 / 2 ^ 43 by positivity]
  · have hxp : 512 ≤ value x := le_of_not_gt h512
    have he := special_exponent x (by rw [abs_of_pos (by linarith)]; exact hxp)
      (by rw [abs_of_pos (by linarith)]; exact hx)
    have hmag : 0 < Wasm.IEEE64.scaledMagnitude x := by
      simp only [Wasm.IEEE64.scaledMagnitude, he, beq_iff_eq,
        show (1032 : Nat) ≠ 0 by norm_num, ite_false]
      positivity
    have hs : Wasm.IEEE64.sign x = false := by
      by_contra hn
      have := (sign_value x hmag).mp (by simpa using hn)
      linarith
    have hv := normal_value x hs (by rw [he]; norm_num)
    rw [he] at hv
    have hf : Wasm.IEEE64.fraction x < 2 ^ 52 := Nat.mod_lt _ (by positivity)
    have hf' : (Wasm.IEEE64.fraction x : ℝ) ≤ 2 ^ 52 - 1 := by
      have : Wasm.IEEE64.fraction x ≤ 2 ^ 52 - 1 := by omega
      have h := (Nat.cast_le (α := ℝ)).mpr this
      push_cast [Nat.one_le_two_pow] at h
      linarith
    rw [hv]
    rw [div_le_iff₀ (by positivity)]
    have h1031 : (2 : ℝ) ^ (1032 - 1) = 2 ^ 1031 := by norm_num
    rw [h1031]
    have : ((2 : ℝ) ^ 52 + (Wasm.IEEE64.fraction x : ℝ)) * 2 ^ 1031 ≤
        ((2 : ℝ) ^ 52 + (2 ^ 52 - 1)) * 2 ^ 1031 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have hnum : ((2 : ℝ) ^ 52 + (2 ^ 52 - 1)) * 2 ^ 1031 = (1024 - 1 / 2 ^ 43) * 2 ^ 1074 := by
      norm_num
    linarith

#print axioms tiny_selected
#print axioms ordinary_selected
#print axioms special_selected
#print axioms overflow_selected
#print axioms underflow_selected
#print axioms big_core_selected
#print axioms neg_infinity_selected
#print axioms nonfinite_selected
#print axioms flag_special
#print axioms flag_big
#print axioms below_top

end Library.Numerics.Float64.Exp2.Exp2Branches
