import Verified.Examples.TgammaRefl8
import Verified.Examples.TgammaInt

/-!
**The path of `tgammaWith` from `-184` to `-3`** within one step of `Γ x` (`reflPath_within`).
`refl_core1` bounds the product `ph + pl` of `asSinpid` and `asExpd`, `refl_core2` derives the
hypotheses of `TgammaRefl8.tail_within` from the specifications of `asLgammaAsym`, `asExpd`, and
`asSinpid`, and `refl_gap` reads `SubnormalGap` at a double below `-170`.  The theorem takes
`FmaSpec.FmaNearest`, `TgammaAsym1.LogdSpec`, `StirlingFact`, `ExpFact`, `TgammaRefl4.SinpidSpec`,
`TgammaRefl4.SubnormalGap`, and the accurate path at the same input as hypotheses.
-/

namespace Verified.Examples.TgammaRefl9
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaFloor TgammaRefl1
  TgammaRefl2 TgammaRefl4 TgammaRefl5 TgammaRefl8

set_option exponentiation.threshold 4096

/-- The words of `π = pih + pil`. -/
theorem pi_words :
    Finite (Float.ofBits 0x400921FB54442D18).toBits ∧ Finite (Float.ofBits 0x3CA1A62633145C07).toBits ∧
      3141592 / 10 ^ 6 ≤ value (Float.ofBits 0x400921FB54442D18).toBits ∧
      value (Float.ofBits 0x400921FB54442D18).toBits ≤ 3141593 / 10 ^ 6 ∧
      |value (Float.ofBits 0x3CA1A62633145C07).toBits| ≤ 1104 / 1000 / 2 ^ 53 ∧
      |value (Float.ofBits 0x400921FB54442D18).toBits + value (Float.ofBits 0x3CA1A62633145C07).toBits -
        Real.pi| ≤ 1 / 10 ^ 20 := by
  have hw1 : Wasm.IEEE64.isFinite 0x400921FB54442D18 = true := by decide
  have hw2 : Wasm.IEEE64.isFinite 0x3CA1A62633145C07 = true := by decide
  rw [TgammaWords.ofBits_value _ hw1, TgammaWords.ofBits_value _ hw2]
  have q1 : (3141592 / 10 ^ 6 : ℚ) ≤ PolyBound.ratOfWord 0x400921FB54442D18 ∧
      PolyBound.ratOfWord 0x400921FB54442D18 ≤ 3141593 / 10 ^ 6 ∧
      PolyBound.qabs (PolyBound.ratOfWord 0x3CA1A62633145C07) ≤ 1104 / 1000 / 2 ^ 53 ∧
      (3141592653589793238462 / 10 ^ 21 : ℚ) ≤
        PolyBound.ratOfWord 0x400921FB54442D18 + PolyBound.ratOfWord 0x3CA1A62633145C07 ∧
      PolyBound.ratOfWord 0x400921FB54442D18 + PolyBound.ratOfWord 0x3CA1A62633145C07 ≤
        3141592653589793238463 / 10 ^ 21 := by decide +kernel
  obtain ⟨a1, a2, a3, a4, a5⟩ := q1
  have cast_le : ∀ a b : ℚ, a ≤ b → (a : ℝ) ≤ (b : ℝ) := fun a b h => by exact_mod_cast h
  have b1 := cast_le _ _ a1
  have b2 := cast_le _ _ a2
  have b3 := cast_le _ _ a3
  have b4 := cast_le _ _ a4
  have b5 := cast_le _ _ a5
  push_cast at b1 b2 b3 b4 b5
  rw [TgammaExpr.qabs_cast] at b3
  have hp1 := Real.pi_gt_d20
  have hp2 := Real.pi_lt_d20
  refine ⟨TgammaWords.ofBits_finite _ hw1, TgammaWords.ofBits_finite _ hw2, b1, b2, b3, ?_⟩
  rw [abs_le]
  constructor <;> linarith

/-- The product `ph + pl` of `asSinpid` and `asExpd`. -/
theorem refl_core1 (vh vl vsh vsl vph vpl s : ℝ) (hs50 : 1 / 2 ^ 50 ≤ s) (hs1 : s ≤ 1)
    (hh1 : 1 / 2 ≤ vh) (hh2 : vh ≤ 5 / 2) (hlow : |vl| ≤ |vh| / 2 ^ 50)
    (hse : |vsh + vsl - s| ≤ s / 2 ^ 58) (hslb : |vsl| ≤ |vsh| / 2 ^ 50)
    (hme : |vph + vpl - (vsh + vsl) * (vh + vl)| ≤ |vl| * |vsl| +
      (4 * (|vh| * |vsl| + |vl| * |vsh|) + |vh| * |vsh| / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1070)
    (hmlow : |vpl| ≤ (|vh| * |vsl| + |vl| * |vsh|) * (1 + 1 / 2 ^ 50) + |vh| * |vsh| / 2 ^ 52 +
      1 / 2 ^ 1070)
    (hmap : |vph - vh * vsh| ≤ |vh| * |vsh| / 2 ^ 53 + 1 / 2 ^ 1075) :
    0 < vsh ∧ 1 / 2 ^ 53 ≤ vph ∧ vph ≤ 3 ∧ |vpl| ≤ vph / 2 ^ 36 ∧
      |vpl| ≤ vph * (1801 / 100 / 2 ^ 53) ∧
      |vph + vpl - (vsh + vsl) * (vh + vl)| ≤ vh * vsh / 2 ^ 97 := by
  have hvh : |vh| = vh := abs_of_pos (by linarith)
  rw [hvh] at hlow hme hmlow hmap
  have hsh : 0 < vsh := by
    by_contra hc
    rw [not_lt] at hc
    rw [abs_of_nonpos hc] at hslb
    have := (abs_le.mp hse).1
    have := (abs_le.mp hslb).2
    have : (0 : ℝ) < s - s / 2 ^ 58 := by linarith
    linarith
  have hvsh : |vsh| = vsh := abs_of_pos hsh
  rw [hvsh] at hslb hme hmlow hmap
  have hshlo : 99 / 100 / 2 ^ 50 ≤ vsh := by
    have := (abs_le.mp hse).1
    have := (abs_le.mp hslb).2
    linarith
  have hshhi : vsh ≤ 101 / 100 := by
    have := (abs_le.mp hse).2
    have := (abs_le.mp hslb).1
    linarith
  have hH : 99 / 200 / 2 ^ 50 ≤ vh * vsh := by nlinarith
  have hH2 : vh * vsh ≤ 26 / 10 := by nlinarith
  have hp1 : vh * |vsl| ≤ vh * vsh / 2 ^ 50 := by
    have := mul_le_mul_of_nonneg_left hslb (by linarith : (0 : ℝ) ≤ vh)
    linarith
  have hp2 : |vl| * vsh ≤ vh * vsh / 2 ^ 50 := by
    have := mul_le_mul_of_nonneg_right hlow hsh.le
    linarith
  have hl2 : |vl| * |vsl| ≤ vh * vsh / 2 ^ 100 := by
    have := mul_le_mul hlow hslb (abs_nonneg _) (by positivity)
    linarith
  have hph := (abs_le.mp hmap).1
  have hph2 := (abs_le.mp hmap).2
  refine ⟨hsh, by linarith, by linarith, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith

/-- The hypotheses of `tail_within` from the specifications. -/
theorem refl_core2 (vx Y vh vl vsh vsl vph vpl vp1 vp2 vrh vrl : ℝ) (E : ℕ)
    (h2 : vx < -3) (hint : ∀ n : ℤ, vx ≠ n)
    (hLe : |Y - Real.log (Real.Gamma (1 - vx))| ≤ 1 / 2 ^ 60)
    (hex : |(vh + vl) * 2 ^ E - Real.exp Y| ≤ Real.exp Y / 2 ^ 59)
    (hh1 : 1 / 2 ≤ vh) (hh2 : vh ≤ 5 / 2) (hlow : |vl| ≤ |vh| / 2 ^ 50)
    (hs50 : 1 / 2 ^ 50 ≤ Real.sin (Real.pi * Int.fract vx))
    (hse : |vsh + vsl - Real.sin (Real.pi * Int.fract vx)| ≤
      Real.sin (Real.pi * Int.fract vx) / 2 ^ 58)
    (hslb : |vsl| ≤ |vsh| / 2 ^ 50) (hsh : 0 < vsh)
    (hph : 1 / 2 ^ 53 ≤ vph) (hpl : |vpl| ≤ vph * (1801 / 100 / 2 ^ 53))
    (hD : |vph + vpl - (vsh + vsl) * (vh + vl)| ≤ vh * vsh / 2 ^ 97)
    (hp1a : 3141592 / 10 ^ 6 ≤ vp1)
    (hp2 : |vp2| ≤ 1104 / 1000 / 2 ^ 53) (hPc : |vp1 + vp2 - Real.pi| ≤ 1 / 10 ^ 20)
    (hrh : |vrh - vp1 / vph| ≤ 1 / |vph| / 2 ^ 49)
    (hR : |vrh + vrl - (vp1 + vp2) / (vph + vpl)| ≤ |(vp1 + vp2) / (vph + vpl)| / 2 ^ 68) :
    1 ≤ E ∧ Real.Gamma vx ≠ 0 ∧ |Real.Gamma vx| < 2 ^ 1021 ∧ 1 ≤ |vrh| ∧ |vrh| ≤ 2 ^ 60 ∧
      |vrh + vrl - |Real.Gamma vx| * 2 ^ E| ≤ 11 * (|Real.Gamma vx| * 2 ^ E) / 2 ^ 60 ∧
      |vrh - |Real.Gamma vx| * 2 ^ E| ≤ 24 * (|Real.Gamma vx| * 2 ^ E) / 2 ^ 53 ∧
      (-170 ≤ ⌊vx⌋ → 1 / 2 ^ 1019 ≤ |Real.Gamma vx|) ∧
      Real.Gamma vx = (if Odd ⌊vx⌋ then -1 else 1) * |Real.Gamma vx| := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sin (Real.pi * Int.fract vx) := ⟨_, rfl⟩
  rw [← hs] at hs50 hse
  have hs1 : s ≤ 1 := by rw [hs]; exact Real.sin_le_one _
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs50
  obtain ⟨Γ1, hΓ1⟩ : ∃ Γ1, Γ1 = Real.Gamma (1 - vx) := ⟨_, rfl⟩
  rw [← hΓ1] at hLe
  have hΓ1g : 1 < Γ1 := by
    have := TgammaAsym6.lgamma_gt (1 - vx) (by linarith)
    rw [← hΓ1] at this
    have hΓp : 0 < Γ1 := by rw [hΓ1]; exact Real.Gamma_pos_of_pos (by linarith)
    by_contra hc
    rw [not_lt] at hc
    have := Real.log_nonpos hΓp.le hc
    linarith
  have hΓ0 : 0 < Γ1 := by linarith
  have hP : (0 : ℝ) < 2 ^ E := by positivity
  -- `Γ x` from the reflection
  have hG := refl_gamma vx hint
  rw [← hs, ← hΓ1] at hG
  have hA : |Real.Gamma vx| = Real.pi / (s * Γ1) := by
    rw [hG, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < Real.pi / (s * Γ1))]
    split_ifs <;> simp
  -- the product and the quotient
  have hQ := exp_close Γ1 Y ((vh + vl) * 2 ^ E) hΓ0 hLe hex
  have hZ := prod_close Γ1 s (2 ^ E) vh vl vsh vsl vph vpl hΓ0 hs0 hP hQ hh1
    (by rw [abs_of_pos (by linarith : (0 : ℝ) < vh)] at hlow; exact hlow) hsh hse
    (by rw [abs_of_pos hsh] at hslb; exact hslb) hD
  obtain ⟨hRT, hrhT⟩ := refl_real Γ1 s (2 ^ E) vph vpl vp1 vp2 vrh vrl hΓ0 hs0 hP hZ
    (by linarith) hpl hp1a hp2 hPc (by rwa [abs_of_pos (by linarith : (0 : ℝ) < vph)] at hrh) hR
  have hT : Real.pi * 2 ^ E / (s * Γ1) = |Real.Gamma vx| * 2 ^ E := by rw [hA]; ring
  rw [hT] at hRT hrhT
  -- `T = |Γ x| 2 ^ E` between `1.17` and `2 ^ 54`
  have hpi := Real.pi_gt_three
  have hpi4 := Real.pi_lt_four
  have hvl : |vl| ≤ vh / 2 ^ 50 := by rwa [abs_of_pos (by linarith : (0 : ℝ) < vh)] at hlow
  have hQlo : Γ1 * (1 - 5 / 2 ^ 60) ≤ (vh + vl) * 2 ^ E := by linarith [(abs_le.mp hQ).1]
  have hQhi : (vh + vl) * 2 ^ E ≤ Γ1 * (1 + 5 / 2 ^ 60) := by linarith [(abs_le.mp hQ).2]
  have hvl1 := (abs_le.mp hvl).1
  have hvl2 := (abs_le.mp hvl).2
  have hPlo : Γ1 * 39 / 100 ≤ 2 ^ E := by
    have : (vh + vl) * 2 ^ E ≤ 251 / 100 * 2 ^ E :=
      mul_le_mul_of_nonneg_right (by linarith) hP.le
    linarith
  have hPhi : 2 ^ E ≤ Γ1 * 21 / 10 := by
    have : 48 / 100 * 2 ^ E ≤ (vh + vl) * 2 ^ E :=
      mul_le_mul_of_nonneg_right (by linarith) hP.le
    linarith
  obtain ⟨T, hTd⟩ : ∃ T, T = |Real.Gamma vx| * 2 ^ E := ⟨_, rfl⟩
  rw [← hTd] at hRT hrhT
  have hTs : T * (s * Γ1) = Real.pi * 2 ^ E := by
    rw [hTd, hA]; field_simp
  have hT0 : 0 < T := by
    rw [hTd]; exact mul_pos (by rw [hA]; positivity) hP
  have hsΓ : s * Γ1 ≤ Γ1 := by nlinarith
  have hTlo : 117 / 100 ≤ T := by
    have e1 : Real.pi * (Γ1 * 39 / 100) ≤ Real.pi * 2 ^ E :=
      mul_le_mul_of_nonneg_left hPlo Real.pi_pos.le
    have e2 : T * (s * Γ1) ≤ T * Γ1 := mul_le_mul_of_nonneg_left hsΓ hT0.le
    have e3 : 3 * Γ1 ≤ Real.pi * Γ1 := mul_le_mul_of_nonneg_right hpi.le hΓ0.le
    by_contra hc
    rw [not_le] at hc
    have := mul_lt_mul_of_pos_right hc hΓ0
    linarith
  have hThi : T ≤ 2 ^ 54 := by
    have e1 : Real.pi * 2 ^ E ≤ 4 * (Γ1 * 21 / 10) := mul_le_mul hpi4.le hPhi hP.le (by norm_num)
    have e2 : T * s ≤ 9 := by
      by_contra hc
      rw [not_le] at hc
      have := mul_lt_mul_of_pos_right hc hΓ0
      have : T * s * Γ1 = T * (s * Γ1) := by ring
      linarith
    have h5 : T * (1 / 2 ^ 50) ≤ T * s := mul_le_mul_of_nonneg_left hs50 hT0.le
    linarith
  have hrh1 := abs_sub_abs_le_abs_sub vrh T
  have hrh2 := abs_sub_abs_le_abs_sub T vrh
  rw [abs_sub_comm] at hrh2
  rw [abs_of_pos hT0] at hrh1 hrh2
  have hΓ6 : 6 ≤ Γ1 := by
    have h4 : Real.Gamma 4 = 6 := by
      have := Real.Gamma_nat_eq_factorial 3
      rw [show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num, show Nat.factorial 3 = 6 from rfl] at this
      rw [this]
      norm_num
    rw [hΓ1, ← h4]
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (by norm_num))
      (Set.mem_Ici.mpr (by linarith)) (by linarith)
  have hE1 : 1 ≤ E := by
    by_contra hc
    have hE0 : E = 0 := by omega
    rw [hE0, pow_zero] at hQlo
    linarith
  rw [← hTd]
  refine ⟨hE1, ?_, ?_, by linarith, by linarith, hRT, hrhT, ?_, ?_⟩
  · intro h0
    rw [h0, abs_zero] at hA
    have : 0 < Real.pi / (s * Γ1) := by positivity
    linarith
  · rw [hA, div_lt_iff₀ (by positivity)]
    have h3 : 1 / 2 ^ 50 ≤ s * Γ1 := le_trans hs50 (le_mul_of_one_le_right hs0.le hΓ1g.le)
    linarith
  · intro hfl
    have hx170 : -170 < vx := by
      have h3 : (-170 : ℝ) ≤ ⌊vx⌋ := by exact_mod_cast hfl
      have h4 := Int.floor_le vx
      rcases (h3.trans h4).lt_or_eq with h5 | h5
      · exact h5
      · exfalso
        apply hint (-170)
        rw [← h5]
        push_cast
        ring
    have hΓ171 : Γ1 ≤ 2 ^ 1020 := by
      have hmono : Γ1 ≤ Real.Gamma 171 := by
        rw [hΓ1]
        exact Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (by linarith))
          (Set.mem_Ici.mpr (by norm_num)) (by linarith)
      have h171 : Real.Gamma 171 = (Nat.factorial 170 : ℝ) := by
        have := Real.Gamma_nat_eq_factorial 170
        rw [show ((170 : ℕ) : ℝ) + 1 = 171 by norm_num] at this
        exact this
      have := TgammaInt.fact_le 170 le_rfl
      rw [h171] at hmono
      linarith [hmono.trans this, (by norm_num : (2 : ℝ) ^ 1020 * (1 - 1 / 2 ^ 30) ≤ 2 ^ 1020)]
    rw [hA, le_div_iff₀ (by positivity)]
    linarith
  · rw [hA]
    exact hG

/-- `SubnormalGap` at a double below `-170`. -/
theorem refl_gap (hGap : SubnormalGap) (x : Float) (h1 : -184 < value x.toBits)
    (h2 : value x.toBits < -170) :
    |Real.Gamma (value x.toBits)| ≤ 1 / 2 ^ 1022 * (1 - 1 / 2 ^ 48) ∨
      1 / 2 ^ 1022 * (1 + 1 / 2 ^ 48) ≤ |Real.Gamma (value x.toBits)| := by
  obtain ⟨k, hk⟩ := grid x.toBits 7 (by norm_num)
    (by rw [abs_of_neg (show value x.toBits < 0 by linarith)]; norm_num; linarith)
  rw [show 52 - 7 = 45 from rfl] at hk
  have hkv : (k : ℝ) = value x.toBits * 2 ^ 45 := by rw [hk]; field_simp
  have hk0 : k < 0 := by
    have : (k : ℝ) < 0 := by rw [hkv]; nlinarith
    exact_mod_cast this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = -k := ⟨(-k).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hmr : (m : ℝ) = -(value x.toBits * 2 ^ 45) := by
    have : ((m : ℤ) : ℝ) = -(k : ℝ) := by rw [hm]; push_cast; ring
    push_cast at this
    rw [this, hkv]
  have hmv : value x.toBits = -(m : ℝ) / 2 ^ 45 := by rw [hmr]; field_simp
  have hm1 : 170 * 2 ^ 45 < m := by
    have : (170 : ℝ) * 2 ^ 45 < m := by rw [hmr]; linarith
    exact_mod_cast this
  have hm2 : m < 184 * 2 ^ 45 := by
    have : (m : ℝ) < 184 * 2 ^ 45 := by rw [hmr]; linarith
    exact_mod_cast this
  have h := hGap m hm1 hm2
  rw [← hmv] at h
  have hz : (2 : ℝ) ^ (-1022 : ℤ) = 1 / 2 ^ 1022 := by
    rw [zpow_neg, one_div]
    congr 1
  rw [hz] at h
  exact h

#print axioms pi_words
#print axioms refl_core1
#print axioms refl_core2
#print axioms refl_gap

end Verified.Examples.TgammaRefl9
