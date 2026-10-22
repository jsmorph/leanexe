import Library.Numerics.Float64.Sinh.SinhWords
import LeanExe.ProofKit.F64NearestBand
import LeanExe.ProofKit.F64NearestDiv

/-!
`Sinh.cosh` within one step of `cosh x` for `0.34657359 ≤ abs(x) < 22`, where the code returns
`0.5 t + 0.5 / t` with `t = exp abs(x)`.  Write `E = exp abs(x)`, `T` for the value of `t`, and
`B` for the rounded quotient.  The exact sum `V = T/2 + B` satisfies
`V - cosh x = (T - E)/2 (1 - 1/(T E)) + (B - 1/(2 T))`, so the error of `T` enters with a factor
below 1/2.  `Library.Numerics.Float64.Exp.ExpTightFloat.exp_near` puts `T` within a spacing `d` of the binade of `cosh x`, plus
`u/16 E` (`mid_band`), and the band `-3d/4 < V - cosh x < d` of
`F64NearestBand.within_of_band` follows: for `cosh x < 2` the error is at most `1.48 u` against
`1.5 u`, and above 2 the quotient is small against the spacing.
-/

namespace Library.Numerics.Float64.Sinh.CoshMid
open CodeLib.IEEE64 LeanExe.ProofKit F64NearestNonnegative SinhWords

set_option exponentiation.threshold 4096

local notation "u" => unitRoundoff64

/-- The band of `V = T/2 + B` around `cosh a`, for `T` within `d + u/16 exp a` of `exp a`, where
`d = Y0 / 2 ^ 52` is the spacing of the binade `[Y0, 2 Y0)` of `cosh a`. -/
theorem mid_band (A T B Y0 d : ℝ) (hA : 34657359 / 10 ^ 8 ≤ A)
    (hd : d = Y0 / 2 ^ 52) (hY : Y0 = 1 ∨ 2 ≤ Y0)
    (hylo : Y0 ≤ Real.cosh A) (hyhi : Real.cosh A < 2 * Y0)
    (hT : |T - Real.exp A| ≤ d + u / 16 * Real.exp A)
    (hB : |B - 1 / (2 * T)| ≤ u * (1 / (2 * T))) :
    T / 2 + B - Real.cosh A < d ∧ Real.cosh A - (T / 2 + B) < 3 / 4 * d := by
  have hu : u = 1 / 2 ^ 53 := rfl
  have hE1 := exp_lower A hA
  have hcosh := cosh_exp A
  generalize Real.exp A = E at hE1 hcosh hT
  rw [hcosh] at hylo hyhi ⊢
  have hE0 : 0 < E := by linarith
  have hEne : E ≠ 0 := hE0.ne'
  have hEi : E * (1 / E) = 1 := by field_simp
  have hi0 : 0 < 1 / E := by positivity
  have hiE : 1 / E ≤ E := by
    rw [div_le_iff₀ hE0]
    nlinarith
  have hY0 : 1 ≤ Y0 := by rcases hY with h | h <;> linarith
  have hdE : d ≤ E / 2 ^ 52 := by rw [hd]; linarith
  have hd0 : 0 < d := by rw [hd]; positivity
  obtain ⟨hT1, hT2⟩ := abs_le.mp hT
  rw [hu] at hT1 hT2
  have hTlo : E * (1 - 1 / 2 ^ 50) ≤ T := by linarith
  have hT14 : 14 / 10 ≤ T := by linarith
  have hT0 : 0 < T := by linarith
  have hTne : T ≠ 0 := hT0.ne'
  have hTE : 1 ≤ T * E := by
    nlinarith [mul_le_mul hT14 (show (14 / 10 : ℝ) ≤ E by linarith) (by norm_num) hT0.le]
  have hid : T / 2 + B - (E + 1 / E) / 2 =
      (T - E) / 2 * (1 - 1 / (T * E)) + (B - 1 / (2 * T)) := by
    field_simp
    ring
  have hF : 1 / (T * E) ≤ 1 := by rw [div_le_one (by positivity)]; exact hTE
  have hF0 : 0 ≤ 1 - 1 / (T * E) := by linarith
  have hF1 : 1 - 1 / (T * E) ≤ 1 := by
    have : 0 ≤ 1 / (T * E) := by positivity
    linarith
  have hR1 : |(T - E) / 2 * (1 - 1 / (T * E))| ≤ (d + u / 16 * E) / 2 := by
    rw [abs_mul, abs_of_nonneg hF0]
    calc |(T - E) / 2| * (1 - 1 / (T * E)) ≤ |(T - E) / 2| * 1 :=
          mul_le_mul_of_nonneg_left hF1 (abs_nonneg _)
      _ = |T - E| / 2 := by rw [abs_div, abs_two, mul_one]
      _ ≤ (d + u / 16 * E) / 2 := by gcongr
  have habs : |T / 2 + B - (E + 1 / E) / 2| ≤ (d + u / 16 * E) / 2 + u * (1 / (2 * T)) := by
    rw [hid]
    exact (abs_add_le _ _).trans (add_le_add hR1 hB)
  obtain ⟨h1, h2⟩ := abs_le.mp habs
  rw [hu] at h1 h2
  have hiT0 : 0 < 1 / (2 * T) := by positivity
  rcases hY with hY1 | hY2
  · rw [hY1] at hd hylo hyhi
    have hE4 : E < 4 := by linarith
    have hiT : 1 / (2 * T) ≤ 3536 / 10000 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    rw [hd] at h1 h2 ⊢
    constructor <;> linarith
  · have h4 : 4 * E ≤ E * E + 1 := by
      have h5 : E * 4 ≤ E * (E + 1 / E) := mul_le_mul_of_nonneg_left (by linarith) hE0.le
      rw [mul_add, hEi] at h5
      linarith
    have hE37 : 37 / 10 ≤ E := by
      by_contra h
      push Not at h
      nlinarith [mul_pos (sub_pos.mpr h) (show 0 < E - 14 / 10 by linarith)]
    have hiT : 1 / (2 * T) ≤ 1 / E := by
      apply one_div_le_one_div_of_le hE0
      linarith
    have hiE' : 1 / E ≤ E / 13 := by
      rw [div_le_div_iff₀ hE0 (by norm_num)]
      nlinarith [mul_self_le_mul_self (by norm_num) hE37]
    rw [hd] at h1 h2 ⊢
    constructor <;> linarith

/-- The middle range on Float. -/
theorem cosh_mid (x : Float) (hxf : Finite x.toBits)
    (hlo : 34657359 / 10 ^ 8 ≤ |value x.toBits|) (hhi : |value x.toBits| < 22) :
    F64SignedRounding.WithinSteps 1 (Real.cosh (value x.toBits))
      (0.5 * Exp.exp x.abs + 0.5 / Exp.exp x.abs).toBits := by
  have hu : u = 1 / 2 ^ 53 := rfl
  obtain ⟨haf, hav⟩ := abs_float x hxf
  rw [← Real.cosh_abs]
  generalize hA : |value x.toBits| = A at hlo hhi hav ⊢
  obtain ⟨se, hn, he⟩ := Library.Numerics.Float64.Exp.ExpTightFloat.exp_near x.abs haf (by rw [hav]; linarith)
    (by rw [hav]; linarith)
  rw [hav] at he
  rw [F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_div, half_bits]
  generalize (Exp.exp x.abs).toBits = t at hn ⊢
  have hE1 := exp_lower A hlo
  have hE22 : Real.exp A ≤ 2 ^ 32 :=
    Library.Numerics.Float64.Exp.ExpTightFloat.exp_le_two_pow A 32 (by push_cast; linarith)
  obtain ⟨hse1, hse2⟩ := abs_le.mp he
  rw [hu] at hse1 hse2
  have htr := F64NearestHalf.nearest_relative se t hn (by linarith) (by linarith)
  obtain ⟨htr1, htr2⟩ := abs_le.mp htr
  rw [hu] at htr1 htr2
  obtain ⟨htf, hts⟩ := nearest_finite se t hn
  set T := value t with hTdef
  have hT1 : 14 / 10 ≤ T := by nlinarith
  have hT2 : T ≤ 2 ^ 33 := by nlinarith
  obtain ⟨hmf, hmv⟩ := mul_half t htf (by linarith)
  have hbn := F64NearestDiv.div_nearest Library.Numerics.Float64.Tanh.Expm1Words.half t half_finite htf half_sign hts
    (by rw [half_value, div_div, le_div_iff₀ (by positivity)]; nlinarith)
    (by rw [half_value, div_div, div_lt_iff₀ (by positivity)]; nlinarith)
  rw [half_value, div_div] at hbn
  set b := Wasm.IEEE64.div Library.Numerics.Float64.Tanh.Expm1Words.half t with hbdef
  have hbr := F64NearestHalf.nearest_relative _ b hbn
    (by rw [le_div_iff₀ (by positivity)]; nlinarith)
    (by rw [div_lt_iff₀ (by positivity)]; nlinarith)
  obtain ⟨hbf, -⟩ := nearest_finite _ b hbn
  obtain ⟨hbr1, hbr2⟩ := abs_le.mp hbr
  have hq0 : 0 < 1 / (2 * T) := by positivity
  have hq1 : 1 / (2 * T) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  rw [hu] at hbr1 hbr2
  have hcn := F64NearestSum.add_nearest _ b hmf hbf (by rw [hmv]; nlinarith)
    (by rw [hmv]; nlinarith)
  rw [hmv] at hcn
  -- The binade of `cosh A`.
  have hy1 : 1 ≤ Real.cosh A := by
    rw [Real.cosh_eq]
    linarith [Real.add_one_le_exp A, Real.add_one_le_exp (-A)]
  have hyE : Real.cosh A ≤ Real.exp A := by
    rw [cosh_exp]
    have : 1 / Real.exp A ≤ Real.exp A := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hyt : Real.cosh A < F64PositiveRounding.overflowThreshold := by
    unfold F64PositiveRounding.overflowThreshold
    have : (2 : ℝ) ^ 32 < 2 ^ 1024 - 2 ^ 970 := by norm_num
    linarith
  obtain ⟨e, -, he2, hylo, hyhi⟩ := F64NearestRelative.binade_of (Real.cosh A)
    (by linarith [show (1 : ℝ) / 2 ^ 1022 ≤ 1 by norm_num]) hyt
  have hT74 : (0 : ℝ) < 2 ^ 1074 := by positivity
  have he1023 : 1023 ≤ e := by
    by_contra h
    have h1 : (2 : ℝ) ^ (e + 52) ≤ 2 ^ 1074 := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ (e + 52) / 2 ^ 1074 ≤ 1 := by rw [div_le_one hT74]; exact h1
    linarith
  have he1055 : e ≤ 1055 := by
    by_contra h
    have h1 : (2 : ℝ) ^ 1107 ≤ 2 ^ (e + 51) := pow_le_pow_right₀ (by norm_num) (by omega)
    have h2 : (2 : ℝ) ^ 1107 / 2 ^ 1074 ≤ 2 ^ (e + 51) / 2 ^ 1074 := by gcongr
    have h3 : (2 : ℝ) ^ 1107 / 2 ^ 1074 = 2 ^ 33 := by norm_num
    linarith
  set Y0 := (2 : ℝ) ^ (e + 51) / 2 ^ 1074 with hY0
  set d := (2 : ℝ) ^ (e - 1) / 2 ^ 1074 with hddef
  have hd : d = Y0 / 2 ^ 52 := by
    rw [hddef, hY0, show e + 51 = (e - 1) + 52 by omega, pow_add]
    field_simp
  have hY2 : (2 : ℝ) ^ (e + 52) / 2 ^ 1074 = 2 * Y0 := by
    rw [hY0, show e + 52 = (e + 51) + 1 by omega, pow_succ]; ring
  have hY4 : (2 : ℝ) ^ (53 + e) / 2 ^ 1074 = 4 * Y0 := by
    rw [hY0, show 53 + e = (e + 51) + 2 by omega, pow_add]; ring
  have hYc : Y0 = 1 ∨ 2 ≤ Y0 := by
    rcases Nat.lt_or_ge e 1024 with h | h
    · left
      rw [hY0, show e + 51 = 1074 by omega, div_self hT74.ne']
    · right
      rw [hY0, le_div_iff₀ hT74]
      calc (2 : ℝ) * 2 ^ 1074 = 2 ^ 1075 := by norm_num
        _ ≤ 2 ^ (e + 51) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [hY2] at hyhi
  -- `T` lies within `d + u/16 exp A` of `exp A`.
  have hTd : |T - se| ≤ d + u / 32 * Real.exp A := by
    by_cases hs : se < (2 : ℝ) ^ (53 + e) / 2 ^ 1074
    · have h := F64NearestHalf.nearest_half se t hn (by linarith) e (by omega) hs
      have h2 : (2 : ℝ) ^ e / 2 / 2 ^ 1074 = d := by
        have h3 : (2 : ℝ) ^ e = 2 ^ (e - 1) * 2 := by rw [← pow_succ]; congr 1; omega
        rw [hddef, h3]
        ring
      rw [h2] at h
      have : 0 ≤ u / 32 * Real.exp A := by rw [hu]; positivity
      linarith
    · push Not at hs
      rw [hY4] at hs
      have hel : (e + 2) * 2 ^ 52 < limit := by unfold limit; omega
      have hv := hn.2 (UInt64.ofNat ((e + 2) * 2 ^ 52)) (by
        rw [F64NearestNonnegative.word_toNat _ hel]; exact hel)
      rw [F64PositiveSpacing.boundary_value (e + 2) (by omega) (by omega),
        show e + 2 + 51 = 53 + e by omega, hY4,
        abs_of_nonpos (show 4 * Y0 - se ≤ 0 by linarith)] at hv
      have hcE : Real.exp A ≤ 2 * Real.cosh A := by
        rw [cosh_exp]
        have : 0 < 1 / Real.exp A := by positivity
        linarith
      have : 0 ≤ d := by positivity
      rw [hu]
      linarith
  have hTE : |T - Real.exp A| ≤ d + u / 16 * Real.exp A := by
    calc |T - Real.exp A| ≤ |T - se| + |se - Real.exp A| := abs_sub_le _ _ _
      _ ≤ (d + u / 32 * Real.exp A) + u / 32 * Real.exp A := add_le_add hTd he
      _ = d + u / 16 * Real.exp A := by ring
  have hB : |value b - 1 / (2 * T)| ≤ u * (1 / (2 * T)) := hbr
  obtain ⟨hup, hdown⟩ := mid_band A T (value b) Y0 d hlo hd hYc hylo hyhi hTE hB
  exact F64NearestBand.within_of_band _ _ _ e (by omega) he2 hylo hyt hcn hup hdown

#print axioms mid_band
#print axioms cosh_mid

end Library.Numerics.Float64.Sinh.CoshMid
