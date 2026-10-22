import Library.Numerics.Float64.Lgamma.LgammaSinpiAbs
import Library.Numerics.Float64.Lgamma.LgammaFastPos
import Library.Numerics.Float64.Tgamma.TgammaAsym3
import Library.Numerics.Float64.Tgamma.TgammaFloor

/-!
The core of the fast path's reflection in `Lgamma.lgammaWith` for `x ≤ -1/2`.  With `a = -x`, the
fractional part `φ = x - ⌊x⌋` (exact by Sterbenz's lemma, `refl_frac`), and `s = sin (π φ)/π`,
the reflection formula gives `ln |Γ x| = -(ln Γ a + ln (a s))` (`refl_L`).  The code computes `s`
(`asSinpipid`), `a s` (`mulDDD`), `ln (a s)` from the high part with the low part's quotient added
(`asLogd`), and the sum with `ln Γ a` from a positive leaf (`sumDD`).  `refl_core` bounds the
result's distance from `ln Γ a + ln (a s)` by the positive leaf's error, the sine's relative error
`ρ` (`2^-72` within `3/256` of an integer, `1.14 · 2^-71/s` elsewhere), `2 · 10^-21` for the
logarithm and the roundings, and the error of `sumDD`.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaReflCore
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaWords LgammaFastSmall
  LgammaPiecePoly TgammaFloor

set_option exponentiation.threshold 4096

/-- **The reflection formula** for a negative non-integer `v`. -/
theorem refl_L (v : ℝ) (hv : v < 0) (hint : ∀ n : ℤ, v ≠ n) :
    Real.log (Real.Gamma v) = -(GammaBasic.lgamma (-v) +
      Real.log (-v * (Real.sin (Real.pi * Int.fract v) / Real.pi))) := by
  have hr := GammaBasic.lgamma_reflect hint
  have hnp : GammaBasic.NotPole (-v) :=
    GammaBasic.notPole_of_neg_one_lt (by linarith) (by linarith)
  have hadd := GammaBasic.lgamma_add_one hnp
  rw [show -v + 1 = 1 - v by ring] at hadd
  rw [hadd] at hr
  have hsp := GammaBasic.sin_pi_fract_pos hint
  have hlogs : Real.log (Real.sin (Real.pi * v)) =
      Real.log (Real.sin (Real.pi * Int.fract v)) := by
    rw [← Real.log_abs (Real.sin (Real.pi * v)), GammaBasic.sin_pi_eq, abs_mul, abs_zpow, abs_neg,
      abs_one, one_zpow, one_mul, abs_of_pos hsp]
  rw [hlogs] at hr
  have hl : Real.log (-v * (Real.sin (Real.pi * Int.fract v) / Real.pi)) =
      Real.log (-v) + (Real.log (Real.sin (Real.pi * Int.fract v)) - Real.log Real.pi) := by
    rw [Real.log_mul (by linarith) (div_pos hsp Real.pi_pos).ne',
      Real.log_div hsp.ne' Real.pi_pos.ne']
  rw [hl]
  rw [GammaBasic.lgamma] at hr
  linarith

/-- **The fractional part** `x - floorF x` of a double from `-2 ^ 52` to `-1/2`: exact, and
`n/2^53` with `0 < n < 2^53`. -/
theorem refl_frac (x : Float) (hx : Finite x.toBits) (h1 : -2 ^ 52 < value x.toBits)
    (h2 : value x.toBits ≤ -1 / 2) (hint : ∀ n : ℤ, value x.toBits ≠ n) :
    Finite (floorF x).toBits ∧ value (floorF x).toBits = ⌊value x.toBits⌋ ∧
      Finite (x - floorF x).toBits ∧ value (x - floorF x).toBits = Int.fract (value x.toBits) ∧
      ∃ n : ℕ, 0 < n ∧ n < 2 ^ 53 ∧ Int.fract (value x.toBits) = n / 2 ^ 53 := by
  set v := value x.toBits with hvdef
  obtain ⟨hff, hfv⟩ := floorF_spec x hx (by rw [abs_of_neg (by linarith)]; linarith)
  have hfl1 : (⌊v⌋ : ℝ) ≤ v := Int.floor_le _
  have hfl2 : v < ⌊v⌋ + 1 := Int.lt_floor_add_one _
  have hfr : 0 < Int.fract v := Int.fract_pos.mpr (hint ⌊v⌋)
  have hfr1 : Int.fract v < 1 := Int.fract_lt_one _
  have hfd : Int.fract v = v - ⌊v⌋ := (Int.self_sub_floor _).symm
  have hfneg : (⌊v⌋ : ℝ) ≤ -1 := by
    have : ⌊v⌋ ≤ -1 := by
      rw [Int.floor_le_iff]; push_cast; linarith
    exact_mod_cast this
  have hd : |v - value (floorF x).toBits| = Int.fract v := by
    rw [hfv, ← hfd, abs_of_pos hfr]
  have hfx : Int.fract v ≤ -v := by
    rcases le_or_gt v (-1) with h | h
    · linarith
    · have : ⌊v⌋ = -1 := by
        rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith
      rw [hfd, this]; push_cast; linarith
  obtain ⟨hsf, hsv⟩ := F64Sterbenz.sub_exact x.toBits (floorF x).toBits hx hff
    (by rw [hd, abs_of_neg (by linarith)]; exact hfx)
    (by rw [hd, hfv, abs_of_neg (by linarith)]; linarith)
    (by rw [hfv, abs_of_neg (by linarith)]; linarith [(by norm_num : (2 : ℝ) ^ 52 + 1 < 2 ^ 1021)])
  rw [← F64Bits.toBits_sub] at hsf hsv
  refine ⟨hff, hfv, hsf, by rw [hsv, hfv, hfd], ?_⟩
  -- `v` lies on the spacing `2 ^ -53`
  have hK : ∃ K : ℤ, v * 2 ^ 53 = K := by
    rcases eq_or_lt_of_le h2 with heq | hlt
    · exact ⟨-2 ^ 52, by rw [heq]; norm_num⟩
    obtain ⟨m, hm⟩ := LgammaFastMid.value_grid x.toBits
    set e := Wasm.IEEE64.exponent x.toBits with hedef
    have he : 1022 ≤ e := by
      by_contra hn
      have hhi := LgammaStir.binade_hi x.toBits e rfl (by omega)
      have : (2 : ℝ) ^ (e + 52) ≤ 2 ^ 1073 := pow_le_pow_right₀ (by norm_num) (by omega)
      have : (2 : ℝ) ^ (e + 52) / 2 ^ 1074 ≤ 2 ^ 1073 / 2 ^ 1074 :=
        div_le_div_of_nonneg_right this (by positivity)
      rw [abs_of_neg (by linarith)] at hhi
      have : (2 : ℝ) ^ 1073 / 2 ^ 1074 = 1 / 2 := by norm_num
      linarith
    have hv53 : v * 2 ^ 53 = (m : ℝ) * 2 ^ (e - 1022) := by
      have h5 : (0 : ℝ) < 2 ^ 1021 := by positivity
      apply mul_right_cancel₀ h5.ne'
      calc v * (2 : ℝ) ^ 53 * 2 ^ 1021 = v * (2 : ℝ) ^ 1074 := by rw [mul_assoc, ← pow_add]
        _ = (m : ℝ) * 2 ^ (e - 1) := hm
        _ = (m : ℝ) * 2 ^ (e - 1022) * 2 ^ 1021 := by rw [mul_assoc, ← pow_add]; congr 2; omega
    exact ⟨(m : ℤ) * 2 ^ (e - 1022), by rw [hv53]; push_cast; ring⟩
  obtain ⟨K, hK⟩ := hK
  set N : ℤ := K - ⌊v⌋ * 2 ^ 53 with hNdef
  have hN : Int.fract v * 2 ^ 53 = N := by
    rw [hfd, sub_mul, hK, hNdef]; push_cast; ring
  have hN0 : 0 < N := by
    have : (0 : ℝ) < N := by rw [← hN]; positivity
    exact_mod_cast this
  have hN1 : N < 2 ^ 53 := by
    have : (N : ℝ) < 2 ^ 53 := by
      rw [← hN]
      have := mul_lt_mul_of_pos_right hfr1 (by positivity : (0 : ℝ) < 2 ^ 53)
      linarith
    exact_mod_cast this
  refine ⟨N.toNat, by omega, by omega, ?_⟩
  rw [eq_div_iff (by positivity), hN]
  have : ((N.toNat : ℕ) : ℤ) = N := Int.toNat_of_nonneg hN0.le
  exact_mod_cast this.symm

/-- `|ln (1 + δ)| ≤ |δ| + 2 ^ -91` for `|δ| ≤ 2 ^ -46`. -/
theorem abs_log_one_add (δ : ℝ) (h : |δ| ≤ 1 / 2 ^ 46) : |Real.log (1 + δ)| ≤ |δ| + 1 / 2 ^ 91 := by
  have := Library.Numerics.Float64.Tgamma.TgammaAsym3.log_one_add δ h
  have h2 := abs_sub_abs_le_abs_sub (Real.log (1 + δ)) δ
  linarith

set_option maxHeartbeats 4000000 in
/-- **The core of the reflection**: `ln Γ a + ln (a s)` against the code's `sumDD`, for `a = -x`
and `s = sin (π φ)/π`, given the double-double `fh + fl` of a positive leaf. -/
theorem refl_core (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (h1 : -2 ^ 52 < value x.toBits) (h2 : value x.toBits ≤ -1 / 2)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (fh fl : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (hfhb : |value fh.toBits| ≤ 2 ^ 897)
    (hflb : |value fl.toBits| ≤ 2 ^ 700) (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD fh fl C.1 (C.2 + B.2 / B.1)) :
    Finite C.1.toBits ∧ Finite D.1.toBits ∧ Finite D.2.toBits ∧ |value C.1.toBits| ≤ 43 ∧
      |value D.1.toBits| ≤ (|value fh.toBits| + 43) * (1 + 1 / 2 ^ 51) + 1 / 2 ^ 1073 ∧
      |value C.1.toBits - Real.log (-value x.toBits *
        (Real.sin (Real.pi * Int.fract (value x.toBits)) / Real.pi))| ≤ 1 / 2 ^ 19 ∧
      |value D.2.toBits| ≤ (|value fl.toBits| + 1 / 2 ^ 20) * (1 + 1 / 2 ^ 51) +
        |value D.1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 ∧
      ∃ ρ : ℝ, (ρ = 1 / 2 ^ 72 ∨ (3 / 256 ≤ 1 / 2 - |Int.fract (value x.toBits) - 1 / 2| ∧
          ρ = 114 / 100 / 2 ^ 71 / (Real.sin (Real.pi * Int.fract (value x.toBits)) / Real.pi))) ∧
        |GammaBasic.lgamma (-value x.toBits) + Real.log (-value x.toBits *
            (Real.sin (Real.pi * Int.fract (value x.toBits)) / Real.pi)) -
          (value D.1.toBits + value D.2.toBits)| ≤
          |GammaBasic.lgamma (-value x.toBits) - (value fh.toBits + value fl.toBits)| + ρ +
            2 / 10 ^ 21 + (3 * (|value fl.toBits| + 1 / 2 ^ 20) + |value D.1.toBits| / 2 ^ 52 +
              1 / 2 ^ 1074) / 2 ^ 53 := by
  obtain ⟨hff, hfv, hdf, hdv, n, hn0, hn, hfn⟩ := refl_frac x hx h1 h2 hint
  set v := value x.toBits with hvdef
  set φ := Int.fract v with hφdef
  have hφ0 : 0 < φ := Int.fract_pos.mpr (hint ⌊v⌋)
  have hφ1 : φ < 1 := Int.fract_lt_one _
  have hsin := GammaBasic.sin_pi_fract_pos hint
  rw [← hφdef] at hsin
  set s := Real.sin (Real.pi * φ) / Real.pi with hsdef
  have hs0 : 0 < s := div_pos hsin Real.pi_pos
  have hs1 : s ≤ 1 / 3 := by
    rw [hsdef, div_le_div_iff₀ Real.pi_pos (by norm_num)]
    have := Real.sin_le_one (Real.pi * φ)
    have := Real.pi_gt_three
    linarith
  -- `s ≥ 2 φ'/π` for `φ' = 1/2 - |φ - 1/2|`
  have hsJ : 2 * (1 / 2 - |φ - 1 / 2|) / 4 ≤ s := by
    have hz0 : 0 ≤ 1 / 2 - |φ - 1 / 2| := by
      rw [sub_nonneg, abs_le]; constructor <;> linarith
    have hsn := LgammaSinpi.sin_eq_near φ
    have h1' := Real.mul_le_sin (x := Real.pi * (1 / 2 - |φ - 1 / 2|))
      (mul_nonneg Real.pi_pos.le hz0) (by
        have : 1 / 2 - |φ - 1 / 2| ≤ 1 / 2 := by linarith [abs_nonneg (φ - 1 / 2)]
        have := mul_le_mul_of_nonneg_left this Real.pi_pos.le
        linarith)
    rw [← mul_assoc, div_mul_cancel₀ 2 Real.pi_ne_zero, ← hsn] at h1'
    rw [hsdef, le_div_iff₀ Real.pi_pos]
    have := Real.pi_lt_four
    nlinarith
  -- the sine
  obtain ⟨hA1, hA2, hAl, hAe⟩ := LgammaSinpiAbs.asSinpipid_abs hF hS (x - floorF x) n hn0 hn hdf
    (by rw [hdv, hfn])
  rw [← hA] at hA1 hA2 hAl hAe
  rw [hdv, ← hsdef] at hAe
  set a1 := value A.1.toBits with ha1def
  set a2 := value A.2.toBits with ha2def
  -- the relative error `δs` of `a1 + a2`
  obtain ⟨ρ, hρ, hρs⟩ : ∃ ρ : ℝ, (ρ = 1 / 2 ^ 72 ∨ (3 / 256 ≤ 1 / 2 - |φ - 1 / 2| ∧
      ρ = 114 / 100 / 2 ^ 71 / s)) ∧ |a1 + a2 - s| ≤ s * ρ ∧ 0 ≤ ρ ∧ ρ ≤ 1 / 2 ^ 60 := by
    rcases hAe with h | ⟨hfar, h⟩
    · refine ⟨1 / 2 ^ 72, Or.inl rfl, ?_, by norm_num, by norm_num⟩
      calc |a1 + a2 - s| ≤ s / 2 ^ 72 := h
        _ = s * (1 / 2 ^ 72) := by ring
    · have hsf : 3 / 512 ≤ s := by linarith
      refine ⟨114 / 100 / 2 ^ 71 / s, Or.inr ⟨hfar, rfl⟩, ?_, by positivity, ?_⟩
      · have e : s * (114 / 100 / 2 ^ 71 / s) = 114 / 100 / 2 ^ 71 := by field_simp
        rw [e]; exact h
      · rw [div_le_iff₀ hs0]
        have : (1 : ℝ) / 2 ^ 60 * (3 / 512) ≤ 1 / 2 ^ 60 * s :=
          mul_le_mul_of_nonneg_left hsf (by norm_num)
        linarith [(by norm_num : (114 : ℝ) / 100 / 2 ^ 71 ≤ 1 / 2 ^ 60 * (3 / 512))]
  obtain ⟨hρ1, hρ0, hρ2⟩ := hρs
  have hsa : s * (1 - 1 / 2 ^ 59) ≤ a1 + a2 ∧ a1 + a2 ≤ s * (1 + 1 / 2 ^ 59) := by
    have := abs_le.mp hρ1
    have hk : s * ρ ≤ s * (1 / 2 ^ 59) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0.le
    constructor <;> linarith
  have ha1b : |a1| ≤ 1 / 2 := by
    have := abs_sub_abs_le_abs_sub a1 (-a2)
    rw [sub_neg_eq_add, abs_neg] at this
    have hpos : 0 < a1 + a2 := by
      have : 0 < s * (1 - 1 / 2 ^ 59) := mul_pos hs0 (by norm_num)
      linarith [hsa.1]
    have : |a1 + a2| ≤ 1 / 3 * (1 + 1 / 2 ^ 59) := by
      rw [abs_of_pos hpos]
      have : s * (1 + 1 / 2 ^ 59) ≤ 1 / 3 * (1 + 1 / 2 ^ 59) :=
        mul_le_mul_of_nonneg_right hs1 (by norm_num)
      linarith [hsa.2]
    have : |a2| ≤ |a1| / 2 ^ 50 := hAl
    linarith
  -- `B = (-x) A`
  obtain ⟨hnxf, hnxv⟩ := LgammaFastTiny.neg_float x hx
  set av := -v with havdef
  have hav : 1 / 2 ≤ av := by rw [havdef]; linarith
  have hav2 : av < 2 ^ 52 := by rw [havdef]; linarith
  have hH : |a1| * |value (-x).toBits| ≤ |a1| * av := by
    rw [hnxv, abs_of_pos (by linarith : (0 : ℝ) < -v)]
  have hLw : |a2| * |value (-x).toBits| ≤ |a1| / 2 ^ 50 * av := by
    rw [hnxv, abs_of_pos (by linarith : (0 : ℝ) < -v)]
    exact mul_le_mul_of_nonneg_right hAl (by linarith)
  have hHm : |a1| * av ≤ 2 ^ 900 := by
    have : |a1| * av ≤ 1 / 2 * 2 ^ 52 := mul_le_mul ha1b hav2.le (by linarith) (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 * 2 ^ 52 ≤ 2 ^ 900)]
  obtain ⟨hB1, hB2, hBe, hB2b, hB1b⟩ := mulDDD_spec hF (-x) A.1 A.2 hnxf hA1 hA2 _ _ hH hLw hHm
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 ≤ 1), abs_nonneg a1])
  rw [← hB] at hB1 hB2 hBe hB2b hB1b
  rw [hnxv] at hBe
  set b1 := value B.1.toBits with hb1def
  set b2 := value B.2.toBits with hb2def
  -- `b1 + b2 = av (a1 + a2) (1 + δm)`
  have hapos : 0 < a1 + a2 := by
    have : 0 < s * (1 - 1 / 2 ^ 59) := mul_pos hs0 (by norm_num)
    linarith [hsa.1]
  have hsav : s / 4 ≤ av * (a1 + a2) := by
    have h1' : 1 / 2 * (a1 + a2) ≤ av * (a1 + a2) := mul_le_mul_of_nonneg_right hav hapos.le
    have h2' : s * (1 - 1 / 2 ^ 59) ≤ a1 + a2 := hsa.1
    linarith
  have hz53 : (1 : ℝ) / 2 ^ 53 ≤ 1 / 2 - |φ - 1 / 2| := by
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hn2 : (n : ℝ) ≤ 2 ^ 53 - 1 := by
      have h3 : n + 1 ≤ 2 ^ 53 := by omega
      have h4 : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ 53 : ℕ) : ℝ) := by exact_mod_cast h3
      push_cast at h4
      linarith
    rw [hfn]
    rcases le_or_gt ((n : ℝ) / 2 ^ 53) (1 / 2) with h | h
    · rw [abs_of_nonpos (by linarith)]
      have : (1 : ℝ) / 2 ^ 53 ≤ n / 2 ^ 53 := by gcongr
      linarith
    · rw [abs_of_pos (by linarith)]
      have : (n : ℝ) / 2 ^ 53 ≤ (2 ^ 53 - 1) / 2 ^ 53 := by gcongr
      have e : ((2 : ℝ) ^ 53 - 1) / 2 ^ 53 = 1 - 1 / 2 ^ 53 := by field_simp
      linarith
  have hsmall : (1 : ℝ) / 2 ^ 56 ≤ s := by linarith
  have hBe' : |b1 + b2 - av * (a1 + a2)| ≤ av * (a1 + a2) / 2 ^ 99 := by
    have hk1 : (3 * (|a1| / 2 ^ 50 * av) + |a1| * av / 2 ^ 51) / 2 ^ 53 ≤
        |a1| * av / 2 ^ 101 := by
      have : (0 : ℝ) ≤ |a1| * av := by positivity
      rw [show (3 * (|a1| / 2 ^ 50 * av) + |a1| * av / 2 ^ 51) / 2 ^ 53 =
        |a1| * av * ((3 / 2 ^ 50 + 1 / 2 ^ 51) / 2 ^ 53) by ring,
        show |a1| * av / 2 ^ 101 = |a1| * av * (1 / 2 ^ 101) by ring]
      exact mul_le_mul_of_nonneg_left (by norm_num) this
    have hk2 : |a1| * av ≤ av * (a1 + a2) * (1 + 1 / 2 ^ 49) := by
      have : |a1| ≤ (a1 + a2) * (1 + 1 / 2 ^ 49) := by
        have h3 := abs_sub_abs_le_abs_sub a1 (-a2)
        rw [sub_neg_eq_add, abs_neg] at h3
        rw [abs_of_pos (by nlinarith : (0 : ℝ) < a1 + a2)] at h3
        have : |a2| ≤ |a1| / 2 ^ 50 := hAl
        nlinarith
      nlinarith
    have hk3 : (1 : ℝ) / 2 ^ 1072 ≤ av * (a1 + a2) / 2 ^ 101 := by
      have : (1 : ℝ) / 2 ^ 56 / 4 / 2 ^ 101 ≤ av * (a1 + a2) / 2 ^ 101 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1072 ≤ 1 / 2 ^ 56 / 4 / 2 ^ 101)]
    have : av * (a1 + a2) * (1 + 1 / 2 ^ 49) / 2 ^ 101 ≤ av * (a1 + a2) / 2 ^ 100 := by
      have : (0 : ℝ) ≤ av * (a1 + a2) := by linarith
      rw [show av * (a1 + a2) * (1 + 1 / 2 ^ 49) / 2 ^ 101 =
        av * (a1 + a2) * ((1 + 1 / 2 ^ 49) / 2 ^ 101) by ring,
        show av * (a1 + a2) / 2 ^ 100 = av * (a1 + a2) * (1 / 2 ^ 100) by ring]
      exact mul_le_mul_of_nonneg_left (by norm_num) this
    have : |a1| * av / 2 ^ 101 ≤ av * (a1 + a2) * (1 + 1 / 2 ^ 49) / 2 ^ 101 :=
      div_le_div_of_nonneg_right hk2 (by norm_num)
    linarith
  -- `|a1| av ≤ P (1 + 2 ^ -49)` for `P = av (a1 + a2)`
  set P := av * (a1 + a2) with hPdef
  have hP0 : 0 < P := by rw [hPdef]; positivity
  have hk2 : |a1| * av ≤ P * (1 + 1 / 2 ^ 49) := by
    have : |a1| ≤ (a1 + a2) * (1 + 1 / 2 ^ 49) := by
      have h3 := abs_sub_abs_le_abs_sub a1 (-a2)
      rw [sub_neg_eq_add, abs_neg, abs_of_pos hapos] at h3
      have : |a2| ≤ |a1| / 2 ^ 50 := hAl
      have : (a1 + a2) * (1 + 1 / 2 ^ 49) = (a1 + a2) + (a1 + a2) / 2 ^ 49 := by ring
      linarith
    rw [hPdef]
    have := mul_le_mul_of_nonneg_right this (by linarith : (0 : ℝ) ≤ av)
    linarith
  have hPs : P ≤ 2 ^ 51 := by
    have : a1 + a2 ≤ 1 / 3 * (1 + 1 / 2 ^ 59) := by
      have : s * (1 + 1 / 2 ^ 59) ≤ 1 / 3 * (1 + 1 / 2 ^ 59) :=
        mul_le_mul_of_nonneg_right hs1 (by norm_num)
      linarith [hsa.2]
    have := mul_le_mul hav2.le this hapos.le (by norm_num)
    rw [hPdef]
    linarith [(by norm_num : (2 : ℝ) ^ 52 * (1 / 3 * (1 + 1 / 2 ^ 59)) ≤ 2 ^ 51)]
  have hPlo : 1 / 2 ^ 58 ≤ P := by linarith
  have hb2 : |b2| ≤ P / 2 ^ 49 := by
    have h1' : |a1| / 2 ^ 50 * av * (1 + 1 / 2 ^ 51) + |a1| * av / 2 ^ 52 ≤
        P * (1 + 1 / 2 ^ 49) * ((1 + 1 / 2 ^ 51) / 2 ^ 50 + 1 / 2 ^ 52) := by
      rw [show |a1| / 2 ^ 50 * av * (1 + 1 / 2 ^ 51) + |a1| * av / 2 ^ 52 =
        |a1| * av * ((1 + 1 / 2 ^ 51) / 2 ^ 50 + 1 / 2 ^ 52) by ring]
      exact mul_le_mul_of_nonneg_right hk2 (by norm_num)
    have h2' : P * (1 + 1 / 2 ^ 49) * ((1 + 1 / 2 ^ 51) / 2 ^ 50 + 1 / 2 ^ 52) ≤
        P * (1 / 2 ^ 49 - 1 / 2 ^ 60) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
    have h3' : (1 : ℝ) / 2 ^ 1071 ≤ P / 2 ^ 60 := by
      have : (1 : ℝ) / 2 ^ 58 / 2 ^ 60 ≤ P / 2 ^ 60 := div_le_div_of_nonneg_right hPlo (by norm_num)
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 1071 ≤ 1 / 2 ^ 58 / 2 ^ 60)]
    have : P * (1 / 2 ^ 49 - 1 / 2 ^ 60) = P / 2 ^ 49 - P / 2 ^ 60 := by ring
    linarith
  have hb1lo : P * (1 - 1 / 2 ^ 48) ≤ b1 := by
    have := abs_le.mp hBe'
    have := abs_le.mp hb2
    have : P / 2 ^ 99 + P / 2 ^ 49 ≤ P / 2 ^ 48 := by
      have : P / 2 ^ 99 ≤ P / 2 ^ 49 := div_le_div_of_nonneg_left hP0.le (by norm_num) (by norm_num)
      linarith
    linarith
  have hb1hi : b1 ≤ P * (1 + 1 / 2 ^ 48) := by
    have := abs_le.mp hBe'
    have := abs_le.mp hb2
    have : P / 2 ^ 99 + P / 2 ^ 49 ≤ P / 2 ^ 48 := by
      have : P / 2 ^ 99 ≤ P / 2 ^ 49 := div_le_div_of_nonneg_left hP0.le (by norm_num) (by norm_num)
      linarith
    linarith
  have hb1p : 0 < b1 := by
    have : 0 < P * (1 - 1 / 2 ^ 48) := mul_pos hP0 (by norm_num)
    linarith
  -- `t = b2/b1`
  have ht : |b2 / b1| ≤ 1 / 2 ^ 48 := by
    rw [abs_div, abs_of_pos hb1p, div_le_iff₀ hb1p]
    have : P / 2 ^ 49 ≤ 1 / 2 ^ 48 * (P * (1 - 1 / 2 ^ 48)) := by
      rw [show 1 / 2 ^ 48 * (P * (1 - 1 / 2 ^ 48)) = P * ((1 - 1 / 2 ^ 48) / 2 ^ 48) by ring,
        show P / 2 ^ 49 = P * (1 / 2 ^ 49) by ring]
      exact mul_le_mul_of_nonneg_left (by norm_num) hP0.le
    have : 1 / 2 ^ 48 * (P * (1 - 1 / 2 ^ 48)) ≤ 1 / 2 ^ 48 * b1 :=
      mul_le_mul_of_nonneg_left hb1lo (by norm_num)
    linarith
  -- the logarithm of `b1`
  obtain ⟨hC1, hC2, hCe, hCl⟩ := LgammaLogd.asLogd_spec hF hL B.1 hB1 hb1p
  rw [← hC] at hC1 hC2 hCe hCl
  set lh := value C.1.toBits with hlhdef
  set ll := value C.2.toBits with hlldef
  have hl2a : (0.6931 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2b : Real.log 2 < 0.6932 := by have := Real.log_two_lt_d9; linarith
  have hlb1 : |Real.log b1| ≤ 42 := by
    have hu : Real.log b1 ≤ 36.1 := by
      have := Real.log_le_log hb1p (show b1 ≤ 2 ^ 52 by
        linarith [(by norm_num : (2 : ℝ) ^ 51 * (1 + 1 / 2 ^ 48) ≤ 2 ^ 52),
          mul_le_mul_of_nonneg_right hPs (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 48)])
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hlo : -41.7 ≤ Real.log b1 := by
      have := Real.log_le_log (by positivity) (show (1 : ℝ) / 2 ^ 60 ≤ b1 by
        have : (1 : ℝ) / 2 ^ 58 * (1 - 1 / 2 ^ 48) ≤ P * (1 - 1 / 2 ^ 48) :=
          mul_le_mul_of_nonneg_right hPlo (by norm_num)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 ≤ 1 / 2 ^ 58 * (1 - 1 / 2 ^ 48))])
      rw [one_div, Real.log_inv, Real.log_pow] at this; push_cast at this; linarith
    rw [abs_le]; constructor <;> linarith
  have hCe' : |lh + ll - Real.log b1| ≤ 1 / 2 ^ 69 + 42 / 2 ^ 78 := by
    have : |Real.log b1| / 2 ^ 78 ≤ 42 / 2 ^ 78 := div_le_div_of_nonneg_right hlb1 (by norm_num)
    linarith
  have hlhb : |lh| ≤ 43 := by
    have h1' := abs_le_three lh ll (Real.log b1)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 69 + 42 / 2 ^ 78 + 42 ≤ 43 - 1 / 2 ^ 21)]
  have hllb : |ll| ≤ 1 / 2 ^ 21 := by
    have : |lh| / 2 ^ 52 ≤ 43 / 2 ^ 52 := div_le_div_of_nonneg_right hlhb (by norm_num)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 22 + 43 / 2 ^ 52 ≤ 1 / 2 ^ 21)]
  -- `q = b2/b1` and `ll' = ll + q`
  have hq := fapprox_div (fapprox_self B.2 hB2) (fapprox_self B.1 hB1) (|b2|) b1 le_rfl
    (le_of_eq (abs_of_pos hb1p).symm) hb1p (1 / 2 ^ 48)
    (by simp only [add_zero, sub_zero]; rw [← abs_of_pos hb1p, ← abs_div]; exact ht)
    (by norm_num)
  have hqe : |value (B.2 / B.1).toBits - b2 / b1| ≤ 1 / 2 ^ 100 := by
    have := hq.2
    simp only [mul_zero, zero_div, zero_add, add_zero, sub_zero] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 48 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 100)]
  have hll' := fapprox_add (fapprox_self C.2 hC2) hq (1 / 2 ^ 20)
    (by
      have := abs_add_le ll (b2 / b1)
      simp only [mul_zero, zero_div, zero_add, add_zero, sub_zero]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 21 + 1 / 2 ^ 48 + (1 / 2 ^ 48 / 2 ^ 53 + 1 / 2 ^ 1075) ≤
        1 / 2 ^ 20)])
    (by norm_num)
  set ll' := C.2 + B.2 / B.1 with hll'def
  have hll'e : |value ll'.toBits - (ll + b2 / b1)| ≤ 11 / 10 / 2 ^ 73 := by
    have := hll'.2
    simp only [mul_zero, zero_div, zero_add, add_zero, sub_zero] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 48 / 2 ^ 53 + 1 / 2 ^ 1075 + 1 / 2 ^ 20 / 2 ^ 53 ≤
      11 / 10 / 2 ^ 73)]
  have hll'b : |value ll'.toBits| ≤ 1 / 2 ^ 20 := by
    have := abs_sub_abs_le_abs_sub (value ll'.toBits) (ll + b2 / b1)
    have := abs_add_le ll (b2 / b1)
    linarith [(by norm_num : (11 : ℝ) / 10 / 2 ^ 73 + 1 / 2 ^ 21 + 1 / 2 ^ 48 ≤ 1 / 2 ^ 20)]
  -- `ln (av s)` against `lh + ll'`
  set δ := (b1 + b2) / (av * s) - 1 with hδdef
  have has : 0 < av * s := by positivity
  have hδb : |δ| ≤ ρ + 1 / 2 ^ 98 := by
    rw [hδdef, show (b1 + b2) / (av * s) - 1 = (b1 + b2 - av * s) / (av * s) by
      field_simp, abs_div, abs_of_pos has, div_le_iff₀ has]
    have e1 : b1 + b2 - av * s = (b1 + b2 - P) + av * (a1 + a2 - s) := by rw [hPdef]; ring
    rw [e1]
    have h1' := abs_add_le (b1 + b2 - P) (av * (a1 + a2 - s))
    have h2' : |av * (a1 + a2 - s)| ≤ av * (s * ρ) := by
      rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < av)]
      exact mul_le_mul_of_nonneg_left hρ1 (by linarith)
    have h3' : P / 2 ^ 99 ≤ av * s * (1 / 2 ^ 98) := by
      have : P ≤ av * (s * (1 + 1 / 2 ^ 59)) := by
        rw [hPdef]; exact mul_le_mul_of_nonneg_left hsa.2 (by linarith)
      have : av * (s * (1 + 1 / 2 ^ 59)) / 2 ^ 99 ≤ av * s * (1 / 2 ^ 98) := by
        rw [show av * (s * (1 + 1 / 2 ^ 59)) / 2 ^ 99 = av * s * ((1 + 1 / 2 ^ 59) / 2 ^ 99) by ring]
        exact mul_le_mul_of_nonneg_left (by norm_num) has.le
      have : P / 2 ^ 99 ≤ av * (s * (1 + 1 / 2 ^ 59)) / 2 ^ 99 :=
        div_le_div_of_nonneg_right (by assumption) (by norm_num)
      linarith
    have : (ρ + 1 / 2 ^ 98) * (av * s) = av * (s * ρ) + av * s * (1 / 2 ^ 98) := by ring
    linarith
  have hδ1 : |δ| ≤ 1 / 2 ^ 46 := by linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 + 1 / 2 ^ 98 ≤ 1 / 2 ^ 46)]
  have hlogδ := abs_log_one_add δ hδ1
  have hlogt := Library.Numerics.Float64.Tgamma.TgammaAsym3.log_one_add (b2 / b1) (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 48 ≤ 1 / 2 ^ 46)])
  have hb12 : b1 + b2 = av * s * (1 + δ) := by
    rw [hδdef]; field_simp; ring
  have hb12p : 0 < b1 + b2 := by
    rw [hb12]; have := abs_le.mp hδ1
    exact mul_pos has (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 46 < 1)])
  have hlog1 : Real.log (b1 + b2) = Real.log (av * s) + Real.log (1 + δ) := by
    rw [hb12, Real.log_mul has.ne' (by have := abs_le.mp hδ1; linarith [(by norm_num : (1 : ℝ) / 2 ^ 46 < 1)])]
  have hlog2 : Real.log (b1 + b2) = Real.log b1 + Real.log (1 + b2 / b1) := by
    rw [← Real.log_mul hb1p.ne' (by
      have := abs_le.mp ht; linarith [(by norm_num : (1 : ℝ) / 2 ^ 48 < 1)])]
    congr 1; field_simp
  have hlogE : |lh + value ll'.toBits - Real.log (av * s)| ≤ ρ + 2 / 10 ^ 21 := by
    have e : lh + value ll'.toBits - Real.log (av * s) = (lh + ll - Real.log b1) +
        (value ll'.toBits - (ll + b2 / b1)) + (b2 / b1 - Real.log (1 + b2 / b1)) +
        Real.log (1 + δ) := by
      linarith [hlog1, hlog2]
    rw [e]
    have := abs_add_le ((lh + ll - Real.log b1) + (value ll'.toBits - (ll + b2 / b1)) +
      (b2 / b1 - Real.log (1 + b2 / b1))) (Real.log (1 + δ))
    have := abs_add_le ((lh + ll - Real.log b1) + (value ll'.toBits - (ll + b2 / b1)))
      (b2 / b1 - Real.log (1 + b2 / b1))
    have := abs_add_le (lh + ll - Real.log b1) (value ll'.toBits - (ll + b2 / b1))
    rw [abs_sub_comm (b2 / b1)] at *
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 69 + 42 / 2 ^ 78 + 11 / 10 / 2 ^ 73 + 1 / 2 ^ 91 +
      1 / 2 ^ 98 + 1 / 2 ^ 91 ≤ 2 / 10 ^ 21)]
  -- `sumDD`
  obtain ⟨hD1, hD2, hDe, hD2b, hD1b⟩ := sumDD_spec fh fl C.1 ll' hfh hfl hC1 hll'.1
    (by linarith [(by norm_num : (2 : ℝ) ^ 897 < 2 ^ 898)])
    (by linarith [(by norm_num : (43 : ℝ) < 2 ^ 898)])
    (|value fl.toBits| + 1 / 2 ^ 20) (by linarith)
    (by linarith [(by norm_num : (2 : ℝ) ^ 700 + 1 / 2 ^ 20 ≤ 2 ^ 800)])
  rw [← hD] at hD1 hD2 hDe hD2b hD1b
  refine ⟨hC1, hD1, hD2, hlhb, ?_, ?_, hD2b, ρ, ?_, ?_⟩
  · have := abs_add_le (value fh.toBits) lh
    have := mul_le_mul_of_nonneg_right (show |value fh.toBits + lh| ≤ |value fh.toBits| + 43 by
      linarith) (by norm_num : (0 : ℝ) ≤ 1 + 1 / 2 ^ 51)
    linarith
  · have := abs_sub_abs_le_abs_sub (lh - Real.log (av * s)) (-value ll'.toBits)
    rw [show lh - Real.log (av * s) - -value ll'.toBits = lh + value ll'.toBits - Real.log (av * s)
      by ring, abs_neg] at this
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 60 + 2 / 10 ^ 21 + 1 / 2 ^ 20 ≤ 1 / 2 ^ 19)]
  · rcases hρ with h | ⟨hfar, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨hfar, h⟩
  · have := abs_sub_le (GammaBasic.lgamma av + Real.log (av * s))
      (value fh.toBits + value fl.toBits + (lh + value ll'.toBits))
      (value D.1.toBits + value D.2.toBits)
    have e2 : GammaBasic.lgamma av + Real.log (av * s) -
        (value fh.toBits + value fl.toBits + (lh + value ll'.toBits)) =
        (GammaBasic.lgamma av - (value fh.toBits + value fl.toBits)) -
          (lh + value ll'.toBits - Real.log (av * s)) := by ring
    rw [e2] at this
    have := abs_sub (GammaBasic.lgamma av - (value fh.toBits + value fl.toBits))
      (lh + value ll'.toBits - Real.log (av * s))
    rw [abs_sub_comm (value fh.toBits + value fl.toBits + (lh + value ll'.toBits))] at *
    linarith

#print axioms refl_L
#print axioms refl_frac
#print axioms refl_core

end Library.Numerics.Float64.Lgamma.LgammaReflCore
