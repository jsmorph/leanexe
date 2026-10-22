import Library.Numerics.Float64.Tanh.TanhTheorem

/-!
`Tanh.tanh` within three steps of `tanh x` on every finite input, and its exceptional results.
The proof selects the branch with `TanhBranches`, converts the Float operations of `core` to
words, and applies `TanhSmall`, `TanhLarge`, and the tiny and huge ranges of `TanhTheorem`.
-/

namespace Library.Numerics.Float64.Tanh.TanhMain
open CodeLib.IEEE64 LeanExe.ProofKit Expm1Branches Expm1Theorem TanhBranches TanhWords
  TanhTheorem

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

/-- Negating a result within `n` steps of `v` gives a result within `n` steps of `-v`. -/
theorem neg_within (n : Nat) (f : Float) (v : ℝ)
    (h : F64SignedRounding.WithinSteps n v f.toBits) :
    F64SignedRounding.WithinSteps n (-v) (-f).toBits := by
  have hn : Wasm.IEEE64.isNaN f.toBits = false := by
    apply Bool.eq_false_iff.mpr
    intro hc
    have h1 := h.1
    simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
      beq_iff_eq, bne_iff_ne, ne_eq] at hc
    omega
  rw [F64Bits.toBits_neg, F64Sign.sub_negZero, hn]
  exact (F64SignedRounding.within_negate n v f.toBits).mpr h

/-- The range `2 ^ -28 ≤ abs(x) < 1` on Float. -/
theorem small_float (x : Float) (hxf : Finite x.toBits) (hlo : 1 / 2 ^ 28 ≤ |value x.toBits|)
    (hhi : |value x.toBits| < 1) :
    F64SignedRounding.WithinSteps 3 (Real.tanh |value x.toBits|)
      ((-Tanh.expm1 (-2.0 * x.abs)) / (Tanh.expm1 (-2.0 * x.abs) + 2.0)).toBits := by
  have hav : value (Wasm.IEEE64.abs x.toBits) = |value x.toBits| := abs_value _
  have haf := abs_finite _ hxf
  obtain ⟨hyf, hyv⟩ := neg_double_value (Wasm.IEEE64.abs x.toBits) haf
    (by rw [hav, abs_abs]; exact le_trans (by norm_num) hlo) (by rw [hav, abs_abs]; linarith)
  have hyb : (-2.0 * x.abs).toBits = Wasm.IEEE64.mul Expm1Words.negTwo
      (Wasm.IEEE64.abs x.toBits) := by
    rw [F64Bits.toBits_mul, negTwo_bits, F64Bits.toBits_abs]
  rw [F64Bits.toBits_div, F64Bits.toBits_neg, F64Bits.toBits_add, two_bits]
  generalize hy : -2.0 * x.abs = y at hyb
  rw [hav] at hyv
  have hyv' : value y.toBits = -(2 * |value x.toBits|) := by rw [hyb]; exact hyv
  have hyf' : Finite y.toBits := by rw [hyb]; exact hyf
  generalize hA : |value x.toBits| = A at hyv' hlo hhi ⊢
  obtain ⟨hθ1lo, hθ1hi, hθ2lo, hθ2hi, -⟩ := Expm1Near.threshold_bounds
  set θ1 := value (UInt64.ofNat (1071001155 * 2 ^ 32))
  set θ2 := value (UInt64.ofNat (1072734898 * 2 ^ 32))
  obtain ⟨e1, e2, e3, e4, -, -⟩ := exp_bounds
  have hP : ∀ b c : ℝ, b ≤ c → Real.exp (-c) ≤ Real.exp (-b) := fun b c h =>
    Real.exp_le_exp.mpr (by linarith)
  have hneg : value y.toBits < 0 := by rw [hyv']; linarith
  rcases lt_or_ge (2 * A) θ1 with h1 | h1
  · obtain ⟨w, S, heq, hwf, hw1, -, hS⟩ := Expm1Near.near_middle y hyf' hneg
      (by rw [hyv']; have : (1 : ℝ) / 2 ^ 54 ≤ 2 * (1 / 2 ^ 28) := by norm_num
          linarith)
      (by rw [hyv', neg_neg]; exact h1)
    rw [heq, neg_bits _ (F64Magnitude.negate_value w hwf).1, F64RelativeStep.negate_negate]
    rw [hyv', neg_neg] at hS
    exact TanhSmall.small_a A w hwf S hlo (by linarith) hw1 hS
  rcases lt_or_ge (2 * A) θ2 with h2 | h2
  · obtain ⟨w, S, heq, hwf, hw1, -, hS⟩ := Expm1Near.near_one y hyf' hneg
      (by rw [hyv', neg_neg]; exact h1) (by rw [hyv', neg_neg]; exact h2)
    rw [heq, neg_bits _ (F64Magnitude.negate_value w hwf).1, F64RelativeStep.negate_negate]
    rw [hyv'] at hS
    have ha := hP _ _ (show 34657359 / 10 ^ 8 ≤ 2 * A by linarith)
    have hb := hP _ _ (show 2 * A ≤ 10397206 / 10 ^ 7 by linarith)
    exact TanhSmall.small_b A w hwf S (by linarith) (by linarith) hw1 hS
  · obtain ⟨w, S, heq, hwf, -, hw2, hS⟩ := Expm1Near.near_k y hyf' hneg
      (by rw [hyv', neg_neg]; exact h2) (by rw [hyv', neg_neg]; linarith)
    rw [heq, neg_bits _ (F64Magnitude.negate_value w hwf).1, F64RelativeStep.negate_negate]
    rw [hyv'] at hS
    have ha := hP _ _ (show 10397205 / 10 ^ 7 ≤ 2 * A by linarith)
    have hb := hP _ _ (show 2 * A ≤ 2 by linarith)
    exact TanhSmall.small_c A w hwf S (by linarith) (by linarith) hw2 hS

/-- The range `1 ≤ abs(x) < 22` on Float. -/
theorem large_float (x : Float) (hxf : Finite x.toBits) (hlo : 1 ≤ |value x.toBits|)
    (hhi : |value x.toBits| < 22) :
    F64SignedRounding.WithinSteps 1 (Real.tanh |value x.toBits|)
      (1.0 - 2.0 / (Tanh.expm1 (2.0 * x.abs) + 2.0)).toBits := by
  have hav : value (Wasm.IEEE64.abs x.toBits) = |value x.toBits| := abs_value _
  have haf := abs_finite _ hxf
  obtain ⟨hyf, hyv⟩ := double_value (Wasm.IEEE64.abs x.toBits) haf
    (by rw [hav, abs_abs]; exact le_trans (by norm_num) hlo) (by rw [hav, abs_abs]; linarith)
  have hyb : (2.0 * x.abs).toBits = Wasm.IEEE64.mul Expm1Words.two
      (Wasm.IEEE64.abs x.toBits) := by
    rw [F64Bits.toBits_mul, two_bits, F64Bits.toBits_abs]
  rw [F64Bits.toBits_sub, F64Bits.toBits_div, F64Bits.toBits_add, two_bits, one_bits]
  generalize hy : 2.0 * x.abs = y at hyb
  rw [hav] at hyv
  have hyv' : value y.toBits = 2 * |value x.toBits| := by rw [hyb]; exact hyv
  have hyf' : Finite y.toBits := by rw [hyb]; exact hyf
  generalize hA : |value x.toBits| = A at hyv' hlo hhi ⊢
  obtain ⟨S, htf, hS0, hc1, hS⟩ := Expm1Near.near_pos y hyf' (by rw [hyv']; linarith)
    (by rw [hyv']; linarith)
  rw [hyv'] at hS
  obtain ⟨-, -, -, -, e5, e6⟩ := exp_bounds
  have hT1 : 638 / 100 ≤ Real.exp (2 * A) - 1 := by
    have := Real.exp_le_exp.mpr (show (2 : ℝ) ≤ 2 * A by linarith)
    linarith
  have hT2 : Real.exp (2 * A) - 1 ≤ 2 ^ 80 := by
    have h1 : Real.exp (2 * A) ≤ Real.exp 44 := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp 44 = Real.exp 1 ^ 44 := by rw [← Real.exp_nat_mul]; norm_num
    have h3 : Real.exp 1 ^ 44 ≤ 3 ^ 44 := pow_le_pow_left₀ (Real.exp_pos 1).le e6 44
    have h4 : (3 : ℝ) ^ 44 ≤ 2 ^ 80 := by norm_num
    linarith
  rw [tanh_large_form]
  exact TanhLarge.large_core _ htf S _ hT1 hT2 hc1 hS

theorem huge_bits :
    (1.0 - Float.ofBits 0x01A56E1FC2F8F359).toBits = Expm1Words.one := by
  rw [F64Bits.toBits_sub, F64Bits.toBits_ofBits, one_bits]
  decide +kernel

/-- `core x` within three steps of `tanh abs(x)` from `2 ^ -28` on. -/
theorem core_within (x : Float) (hxf : Finite x.toBits) (hlo : 1 / 2 ^ 28 ≤ |value x.toBits|) :
    F64SignedRounding.WithinSteps 3 (Real.tanh |value x.toBits|) (core x).toBits := by
  unfold core
  by_cases h22 : highWord x.toBits < 1077280768
  · rw [ite_eq_left h22]
    have hhi := high_lt_real x.toBits 1077280768 (by norm_num) 22 22 (by norm_num)
      (by decide +kernel) (UInt64.lt_iff_toNat_lt.mp h22)
    by_cases h1 : highWord x.toBits ≥ 1072693248
    · rw [ite_eq_left h1]
      have hge := high_ge_real x.toBits 1072693248 (by norm_num) 1 1 (by norm_num)
        (by decide +kernel) (UInt64.le_iff_toNat_le.mp h1)
      exact within_mono 1 3 (by norm_num) _ _ (large_float x hxf hge hhi)
    · rw [ite_eq_right h1]
      have h1n : (highWord x.toBits).toNat < 1072693248 := by
        have : ¬ 1072693248 ≤ (highWord x.toBits).toNat :=
          fun h => h1 (UInt64.le_iff_toNat_le.mpr h)
        omega
      have hlt := high_lt_real x.toBits 1072693248 (by norm_num) 1 1 (by norm_num)
        (by decide +kernel) h1n
      exact small_float x hxf hlo hlt
  · rw [ite_eq_right h22, huge_bits]
    have h22n : 1077280768 ≤ (highWord x.toBits).toNat := by
      have : ¬ (highWord x.toBits).toNat < 1077280768 :=
        fun h => h22 (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    have hge := high_ge_real x.toBits 1077280768 (by norm_num) 22 22 (by norm_num)
      (by decide +kernel) h22n
    exact within_mono 1 3 (by norm_num) _ _ (huge_within _ hge)

/-- `Tanh.tanh` lies within three steps of `tanh x` on every finite input. -/
theorem tanh_within_three (x : Float) (hxf : Finite x.toBits) :
    F64SignedRounding.WithinSteps 3 (Real.tanh (value x.toBits)) (Tanh.tanh x).toBits := by
  have h1 := high_finite x.toBits hxf
  by_cases ht : highWord x.toBits < 1043333120
  · have hx := high_lt_real x.toBits 1043333120 (by norm_num) (1 / 2 ^ 28) (1 / 2 ^ 28)
      (by norm_num) (by decide +kernel) (UInt64.lt_iff_toNat_lt.mp ht)
    rw [select_tiny x h1 ht (huge_add_gt x hxf (hx.trans (by norm_num)))]
    exact within_mono 1 3 (by norm_num) _ _ (tiny_within _ hxf hx)
  · have htn : 1043333120 ≤ (highWord x.toBits).toNat := by
      have : ¬ (highWord x.toBits).toNat < 1043333120 :=
        fun h => ht (UInt64.lt_iff_toNat_lt.mpr h)
      omega
    have hlo := high_ge_real x.toBits 1043333120 (by norm_num) (1 / 2 ^ 28) (1 / 2 ^ 28)
      (by norm_num) (by decide +kernel) htn
    have hX0 : 0 < |value x.toBits| := lt_of_lt_of_le (by positivity) hlo
    rw [select_main x h1 (fun h => ht h.1)]
    have hc := core_within x hxf hlo
    cases hs : sgn x.toBits
    · have hpos := pos_of_sgn x.toBits hs hX0
      rw [abs_of_pos hpos] at hc
      simpa using hc
    · have hneg := neg_of_sgn x.toBits hs hX0
      rw [abs_of_neg hneg, Real.tanh_neg] at hc
      have h := neg_within 3 _ _ hc
      rw [neg_neg] at h
      simpa using h

#print axioms small_float
#print axioms large_float
#print axioms core_within
#print axioms tanh_within_three

end Library.Numerics.Float64.Tanh.TanhMain
