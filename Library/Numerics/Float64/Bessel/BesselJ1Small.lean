import Library.Numerics.Float64.Bessel.BesselSmallJ1

/-!
`Bessel.j1 x` for `|x| < 2`.  Below `2^-27` the code returns `0.5 x`, which lies within
`2^-81 + 2^-1075` of `x/2` (`half_tiny`), and `J₁(x)` lies within `|x|³/8` of `x/2` (`j1_lin`).
From `2^-27` on, `BesselSmallJ1.piece_k` and `BesselSmallApprox.j1_approx` bound the error on five
ranges of `|x|` (`form_bound`).  `j1_small` bounds the error by `j1Err |x|`: `1.4 u` up to 1, then
`1.74 u`, `2.26 u`, `2.98 u`, and `3.89 u` on the ranges that end at `5/4`, `3/2`, `7/4`, and 2.
`j1_zero` gives the value 0 at both zeros, where `J₁` vanishes.
-/

namespace Library.Numerics.Float64.Bessel.BesselJ1Small
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large BesselSmallJ0
  BesselSmallJ1
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- `J₁ x = x/2` up to `|x|³/8` for `|x| ≤ 2`. -/
theorem j1_lin (v : ℝ) (hv : |v| ≤ 2) : |J1 v - v / 2| ≤ |v| ^ 3 / 8 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, q0, q1, -⟩ := coeff_facts
  obtain ⟨hz0, hz1⟩ := zeta_facts v hv
  have hr := a1_remainder (v ^ 2 / 4) (by rw [abs_of_nonneg hz0]; exact hz1) 1 le_rfl
  have e : eval (a1List 1) (v ^ 2 / 4) = 1 := by
    simp only [a1List, List.range_succ, List.range_zero, List.nil_append, List.map_cons,
      List.map_nil, eval_cons, eval_nil]
    rw [q0]
    push_cast
    ring
  have ha : |a1 1| = 1 / 2 := by rw [a1, ← qabs_cast, q1]; norm_num
  rw [e, ha, abs_of_nonneg hz0, pow_one] at hr
  have h : J1 v - v / 2 = v / 2 * (psum a1 (v ^ 2 / 4) - 1) := by unfold J1; ring
  rw [h, abs_mul, abs_div, abs_two]
  calc |v| / 2 * |psum a1 (v ^ 2 / 4) - 1| ≤ |v| / 2 * (2 * (1 / 2) * (v ^ 2 / 4)) :=
        mul_le_mul_of_nonneg_left hr (by positivity)
    _ = |v| ^ 3 / 8 := by rw [← sq_abs v]; ring

/-- `0.5 x` for `|x| ≤ 2^-27`. -/
theorem half_tiny (x : Float) (hf : Finite x.toBits) (h : |value x.toBits| ≤ 1 / 2 ^ 27) :
    FApprox (0.5 * x) (value x.toBits / 2) (1 / 2 ^ 81 + 1 / 2 ^ 1075) := by
  have h05 : FApprox (0.5 : Float) (1 / 2) 0 := by
    unfold FApprox Approx
    have hb : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
    rw [hb, ← ratOfWord_cast]
    have : ratOfWord 0x3FE0000000000000 = 1 / 2 := by decide +kernel
    rw [this]
    exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩
  have hm := fapprox_mul h05 (fapprox_exact x hf) (1 / 2) (1 / 2 ^ 27) (by norm_num) h
    (1 / 2 ^ 28) (by norm_num) (by norm_num)
  exact fmono (fcongr hm (by ring)) (le_of_eq (by norm_num))

/-- The error bound of `j1` below 2, by the range of `|x|`. -/
noncomputable def j1Err (w : ℝ) : ℝ :=
  if w ≤ 1 then 14 / 10 * 𝐮 else if w ≤ 5 / 4 then 174 / 100 * 𝐮
  else if w ≤ 3 / 2 then 226 / 100 * 𝐮 else if w ≤ 7 / 4 then 298 / 100 * 𝐮 else 389 / 100 * 𝐮

theorem j1Err_le (w : ℝ) : j1Err w ≤ 389 / 100 * 𝐮 := by
  have hu : (0 : ℝ) ≤ 𝐮 := by unfold unitRoundoff64; positivity
  unfold j1Err
  split_ifs <;> linarith

/-- A result within `E` of the first form lies within `E + |x| (0.005 u + 2^-99)` of `J₁`. -/
theorem form_bound {T : Float} {v E : ℝ} (hv : |v| ≤ 2)
    (h : FApprox T (v / 2 + v * (v ^ 2 * eval R1 (v ^ 2)) / eval S1 (v ^ 2)) E) :
    Finite T.toBits ∧ |value T.toBits - J1 v| ≤ E + |v| * (5 / 1000 * 𝐮 + 1 / 2 ^ 99) := by
  refine ⟨h.1, ?_⟩
  have h1 := h.2
  have h2 := j1_approx v hv
  have h3 := abs_sub_le (value T.toBits) (v / 2 + v * (v ^ 2 * eval R1 (v ^ 2)) / eval S1 (v ^ 2))
    (J1 v)
  have h4 : |v / 2 + v * (v ^ 2 * eval R1 (v ^ 2)) / eval S1 (v ^ 2) - J1 v| =
      |J1 v - (v / 2 + v * (v ^ 2 * eval R1 (v ^ 2)) / eval S1 (v ^ 2))| := abs_sub_comm _ _
  linarith

theorem value_neg_zero : value (0x8000000000000000 : UInt64) = 0 := by
  rw [← ratOfWord_cast]
  have : ratOfWord 0x8000000000000000 = 0 := by decide +kernel
  rw [this]
  norm_num

/-- `j1` for `|x| < 2`. -/
theorem j1_small (x : Float) (hxf : Finite x.toBits)
    (h2 : x.toBits.toNat % 2 ^ 63 < 0x4000000000000000) :
    Finite (Bessel.j1 x).toBits ∧
      |value (Bessel.j1 x).toBits - J1 (value x.toBits)| ≤ j1Err |value x.toBits| := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hab := F64Bits.toBits_abs x
  have hN := Library.Numerics.Float64.Trig.TrigSinCos.abs_toNat x.toBits
  have hav : value x.abs.toBits = |value x.toBits| := by rw [hab, Library.Numerics.Float64.Trig.TrigSinCos.abs_value]
  have haN : x.abs.toBits.toNat = x.toBits.toNat % 2 ^ 63 := by rw [hab, hN]
  have hw2 : |value x.toBits| < 2 := by
    have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
      (right := (0x4000000000000000 : UInt64)) (by decide) (by rw [haN]; exact h2)
    rw [value_two, hav] at h
    exact h
  have hixN := Library.Numerics.Float64.Trig.TrigSinCos.high_word x.toBits
  have hfin := Library.Numerics.Float64.Trig.TrigSinCos.finite_bound x.toBits hxf
  unfold Bessel.j1 Bessel.j1With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 1073741824) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  have hbig := huge_add x hxf hw2.le
  by_cases h27 : x.toBits >>> 32 &&& 2147483647 < 1044381696
  · rw [ite_eq_left (by simp [h27, hbig])]
    have hsmall : |value x.toBits| < 1 / 2 ^ 27 := by
      have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
        (right := (0x3E40000000000000 : UInt64)) (by decide) (by
          rw [haN]
          simp only [UInt64.reduceToNat]
          have := UInt64.lt_iff_toNat_lt.mp h27
          rw [hixN] at this
          simp only [UInt64.reduceToNat] at this
          omega)
      have e : value (0x3E40000000000000 : UInt64) = 1 / 2 ^ 27 := by
        rw [← ratOfWord_cast]
        have : ratOfWord 0x3E40000000000000 = 1 / 2 ^ 27 := by decide +kernel
        rw [this]; norm_num
      rw [e, hav] at h
      exact h
    have hh := half_tiny x hxf hsmall.le
    refine ⟨hh.1, ?_⟩
    have hl := j1_lin (value x.toBits) hw2.le
    have h3 : |value x.toBits| ^ 3 ≤ (1 / 2 ^ 27) ^ 3 :=
      pow_le_pow_left₀ (abs_nonneg _) hsmall.le 3
    have h4 := abs_sub_le (value (0.5 * x).toBits) (value x.toBits / 2) (J1 (value x.toBits))
    have h5 : |value x.toBits / 2 - J1 (value x.toBits)| = |J1 (value x.toBits) - value x.toBits / 2| :=
      abs_sub_comm _ _
    unfold j1Err
    rw [ite_eq_left (by linarith : |value x.toBits| ≤ 1)]
    have h6 := hh.2
    rw [hu]
    norm_num at h3 h6 ⊢
    linarith
  · rw [ite_eq_right (by simp [h27])]
    have hn : ¬ (1044381696 : UInt64).toNat > (x.toBits >>> 32 &&& 2147483647).toNat :=
      fun h => h27 (UInt64.lt_iff_toNat_lt.mpr h)
    rw [hixN] at hn
    simp only [UInt64.reduceToNat] at hn
    have he : 2 ≤ Wasm.IEEE64.exponent x.toBits := by
      change 2 ≤ x.toBits.toNat / 2 ^ 52 % 2 ^ 11
      omega
    have ha : 1 / 134217728 ≤ |value x.toBits| := by
      have h := (F64PositiveOrder.value_le_iff (left := (0x3E40000000000000 : UInt64))
        (right := x.abs.toBits) (by decide) (by rw [haN]; omega)).mpr (by
          rw [haN]
          simp only [UInt64.reduceToNat]
          omega)
      have e : value (0x3E40000000000000 : UInt64) = 1 / 134217728 := by
        rw [← ratOfWord_cast]
        have : ratOfWord 0x3E40000000000000 = 1 / 134217728 := by decide +kernel
        rw [this]; norm_num
      rw [e, hav] at h
      exact h
    show Finite (x * 0.5 + x * x * hornerF (r1w.map Float.ofBits) (x * x) * x /
        hornerF (1.0 :: s1w.map Float.ofBits) (x * x)).toBits ∧ _
    set v := value x.toBits with hv
    have hv2 := hw2.le
    have hk : 0 ≤ 5 / 1000 * 𝐮 + 1 / 2 ^ 99 := by rw [hu]; positivity
    unfold j1Err
    rcases le_or_gt |v| 1 with c1 | c1
    · obtain ⟨hf, hb⟩ := form_bound hv2 (piece_0 x hxf he v hv.symm ha c1)
      refine ⟨hf, hb.trans ?_⟩
      rw [ite_eq_left c1]
      have := mul_le_mul_of_nonneg_right c1 hk
      rw [hu] at this ⊢
      norm_num at this ⊢
      linarith
    rw [ite_eq_right (not_le.mpr c1)]
    rcases le_or_gt |v| (5 / 4) with c2 | c2
    · obtain ⟨hf, hb⟩ := form_bound hv2 (piece_1 x hxf he v hv.symm c1.le c2)
      refine ⟨hf, hb.trans ?_⟩
      rw [ite_eq_left c2]
      have := mul_le_mul_of_nonneg_right c2 hk
      rw [hu] at this ⊢
      norm_num at this ⊢
      linarith
    rw [ite_eq_right (not_le.mpr c2)]
    rcases le_or_gt |v| (3 / 2) with c3 | c3
    · obtain ⟨hf, hb⟩ := form_bound hv2 (piece_2 x hxf he v hv.symm c2.le c3)
      refine ⟨hf, hb.trans ?_⟩
      rw [ite_eq_left c3]
      have := mul_le_mul_of_nonneg_right c3 hk
      rw [hu] at this ⊢
      norm_num at this ⊢
      linarith
    rw [ite_eq_right (not_le.mpr c3)]
    rcases le_or_gt |v| (7 / 4) with c4 | c4
    · obtain ⟨hf, hb⟩ := form_bound hv2 (piece_3 x hxf he v hv.symm c3.le c4)
      refine ⟨hf, hb.trans ?_⟩
      rw [ite_eq_left c4]
      have := mul_le_mul_of_nonneg_right c4 hk
      rw [hu] at this ⊢
      norm_num at this ⊢
      linarith
    rw [ite_eq_right (not_le.mpr c4)]
    obtain ⟨hf, hb⟩ := form_bound hv2 (piece_4 x hxf he v hv.symm c4.le hv2)
    refine ⟨hf, hb.trans ?_⟩
    have := mul_le_mul_of_nonneg_right hv2 hk
    rw [hu] at this ⊢
    norm_num at this ⊢
    linarith

/-- At both zeros, `x` and `j1 x` have the value 0. -/
theorem j1_zero (x : Float) (h0 : x.toBits.toNat % 2 ^ 63 = 0) :
    value x.toBits = 0 ∧ value (Bessel.j1 x).toBits = 0 := by
  have hlt := x.toBits.toNat_lt
  have hx : x.toBits = 0 ∨ x.toBits = 0x8000000000000000 := by
    have : x.toBits.toNat = 0 ∨ x.toBits.toNat = 2 ^ 63 := by omega
    rcases this with h | h
    · exact Or.inl (UInt64.toNat_inj.mp (by rw [h]; rfl))
    · exact Or.inr (UInt64.toNat_inj.mp (by rw [h]; rfl))
  have hxf : Finite x.toBits := by
    rcases hx with h | h <;> rw [h] <;> unfold CodeLib.IEEE64.Finite <;> decide
  have hv : value x.toBits = 0 := by
    rcases hx with h | h
    · rw [h, F64Magnitude.value_zero]
    · rw [h, value_neg_zero]
  have hixN := Library.Numerics.Float64.Trig.TrigSinCos.high_word x.toBits
  have hbig := huge_add x hxf (by rw [hv, abs_zero]; norm_num)
  unfold Bessel.j1 Bessel.j1With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 1073741824) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  have h27 : x.toBits >>> 32 &&& 2147483647 < 1044381696 := by
    rw [UInt64.lt_iff_toNat_lt, hixN]; simp only [UInt64.reduceToNat]; omega
  rw [ite_eq_left (by simp [h27, hbig])]
  refine ⟨hv, ?_⟩
  have hb : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
  rw [F64Bits.toBits_mul, hb]
  rcases hx with h | h
  · rw [h, show Wasm.IEEE64.mul 0x3FE0000000000000 0 = 0 by decide +kernel, F64Magnitude.value_zero]
  · rw [h, show Wasm.IEEE64.mul 0x3FE0000000000000 0x8000000000000000 = 0x8000000000000000 by
      decide +kernel, value_neg_zero]

#print axioms j1_lin
#print axioms half_tiny
#print axioms form_bound
#print axioms j1_small
#print axioms j1_zero

end Library.Numerics.Float64.Bessel.BesselJ1Small
