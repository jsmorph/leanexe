import Library.Numerics.Float64.Log1p.Log1pTheoremReduce
import LeanExe.ProofKit.F64ErrorTrack

/-!
The correction `c/u` of `Log1p.log1p` against `t = (1 + x - u)/u`, the relative rounding error of
`u = 1 + x`.  For `x ≤ -1/2` the sum is exact and `c = 0`.  For `-1/2 < x ≤ -0.2928`, and for
`0.4142 ≤ x ≤ 1 - 2 ^ -52`, `u - 1` is exact by Sterbenz's lemma and `x - (u - 1)` rounds a
value below `2 ^ -52`.  For `1 ≤ x < 2 ^ 53`, `u - x` and `1 - (u - x)` are exact on the grid of
`x`.  In each case `c/u` lies within `2 ^ -60` of `t`, and `abs t ≤ 2 ^ -52`.  `log_split` turns
`log (1 + x)` into `K log 2 + log (1 + f) + log (1 + t)`.
-/

namespace Library.Numerics.Float64.Log1p.Log1pTheoremCorr
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest Log1pTheoremBranches
  Log1pTheoremTail Log1pTheoremReduce

set_option exponentiation.threshold 4096

theorem log_split (vx vu vf t : ℝ) (K : ℤ) (hu : vu = 2 ^ K * (1 + vf)) (hf : -1 < vf)
    (hvu : 0 < vu) (ht : t = (1 + vx - vu) / vu) (hx : -1 < vx) :
    Real.log (1 + vx) = K * Real.log 2 + Real.log (1 + vf) + Real.log (1 + t) := by
  have h1 : 1 + t = (1 + vx) / vu := by
    rw [ht]
    field_simp
    ring
  rw [h1, Real.log_div (by linarith : (0 : ℝ) < 1 + vx).ne' hvu.ne', hu,
    Real.log_mul (by positivity) (by linarith : (0 : ℝ) < 1 + vf).ne', Real.log_zpow]
  ring

theorem one_approx : FApprox (1.0 : Float) 1 0 :=
  ⟨one_float.1, by rw [one_float.2, sub_self, abs_zero]⟩

theorem one_scaled : Wasm.IEEE64.scaledValue (1.0 : Float).toBits = 2 ^ 1074 := by
  rw [show (1.0 : Float).toBits = 0x3FF0000000000000 from rfl]
  decide +kernel

/-- The test of `cOf` on `k`. -/
theorem k_cases (u : Float) (hu : Finite u.toBits) (h0 : 0 < value u.toBits) :
    (value u.toBits < 1 → (kOf u >>> 63 == 0 && kOf u != 0) = false) ∧
    (1 ≤ value u.toBits → value u.toBits < 2 → (kOf u >>> 63 == 0 && kOf u != 0) = false) ∧
    (2 ≤ value u.toBits → (kOf u >>> 63 == 0 && kOf u != 0) = true) := by
  set w := u.toBits with hw
  have hw63 := pos_word w h0
  have hk := k_nat u
  rw [← hw] at hk
  have hexp : Wasm.IEEE64.exponent w = w.toNat / 2 ^ 52 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have he2 : w.toNat / 2 ^ 52 < 2047 := by
    have h := hu
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hexp, bne_iff_ne, ne_eq] at h
    omega
  have hsh : (kOf u >>> 63).toNat = (kOf u).toNat / 2 ^ 63 := by
    rw [UInt64.toNat_shiftRight, show (63 : UInt64).toNat % 64 = 63 from rfl,
      Nat.shiftRight_eq_div_pow]
  have habs : |value w| = value w := abs_of_pos h0
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h1 => ?_⟩
  · have he : w.toNat / 2 ^ 52 ≤ 1022 := by
      by_contra hc
      have := F64Magnitude.magnitude_ge w 1023 0 (by norm_num) (by norm_num) (by norm_num)
        (by rw [hexp]; omega)
      rw [habs] at this
      norm_num at this
      linarith
    have h3 : (kOf u >>> 63 == 0) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      intro h
      have := congrArg UInt64.toNat h
      rw [hsh, hk] at this
      simp at this
      omega
    simp [h3]
  · have he : w.toNat / 2 ^ 52 = 1023 := by
      have ha : 1023 ≤ w.toNat / 2 ^ 52 := by
        by_contra hc
        have := F64Magnitude.magnitude_lt w 1023 0 (by norm_num) (by norm_num) (by rw [hexp]; omega)
        rw [habs] at this
        norm_num at this
        linarith
      have hb : w.toNat / 2 ^ 52 ≤ 1023 := by
        by_contra hc
        have := F64Magnitude.magnitude_ge w 1024 1 (by norm_num) (by norm_num) (by norm_num)
          (by rw [hexp]; omega)
        rw [habs] at this
        norm_num at this
        linarith
      omega
    have h3 : (kOf u != 0) = false := by
      simp only [bne_eq_false_iff_eq]
      apply UInt64.toNat_inj.mp
      rw [hk, he]
      rfl
    simp [h3]
  · have he : 1024 ≤ w.toNat / 2 ^ 52 := by
      by_contra hc
      have := F64Magnitude.magnitude_lt w 1024 1 (by norm_num) (by norm_num) (by rw [hexp]; omega)
      rw [habs] at this
      norm_num at this
      linarith
    have h3 : (kOf u >>> 63 == 0) = true := by
      simp only [beq_iff_eq]
      apply UInt64.toNat_inj.mp
      rw [hsh, hk]
      simp
      omega
    have h4 : (kOf u != 0) = true := by
      simp only [bne_iff_ne, ne_eq]
      intro h
      have := congrArg UInt64.toNat h
      rw [hk] at this
      simp at this
      omega
    simp [h3, h4]

/-- A word's scaled value is a multiple of `2 ^ (exponent - 1)`. -/
theorem scaled_dvd (w : UInt64) (s : ℕ) (hs : s ≤ Wasm.IEEE64.exponent w - 1) :
    (2 : ℤ) ^ s ∣ Wasm.IEEE64.scaledValue w := by
  obtain ⟨M, -, hM⟩ := F64Exact.magnitude_grid w
  have h : (2 : ℕ) ^ s ∣ Wasm.IEEE64.scaledMagnitude w := by
    rw [hM]
    exact Dvd.dvd.mul_left (pow_dvd_pow 2 hs) M
  obtain ⟨q, hq⟩ := h
  simp only [Wasm.IEEE64.scaledValue]
  split
  · exact ⟨-(q : ℤ), by rw [hq]; push_cast; ring⟩
  · exact ⟨q, by rw [hq]; push_cast; ring⟩

/-- The exponent field of a word of magnitude at least `2 ^ q`. -/
theorem exponent_ge (w : UInt64) (e : ℕ) (q : ℤ) (he1 : 1 ≤ e) (hq : (e : ℤ) = q + 1023)
    (h : (2 : ℝ) ^ q ≤ |value w|) : e ≤ Wasm.IEEE64.exponent w := by
  by_contra hc
  have := F64Magnitude.magnitude_lt w e q he1 hq (by omega)
  linarith

theorem scaled_of_value (w : UInt64) (v : ℝ) (h : value w = v) :
    (Wasm.IEEE64.scaledValue w : ℝ) = v * 2 ^ 1074 := by
  rw [← h, value]
  field_simp

/-- `x ≤ -1/2`: `u = 1 + x` exactly and `c = 0`. -/
theorem corr_low (x : Float) (hx : Finite x.toBits) (h1 : -1 < value x.toBits)
    (h2 : value x.toBits ≤ -1 / 2) :
    Finite (1.0 + x).toBits ∧ value (1.0 + x).toBits = 1 + value x.toBits ∧
      1 / 2 ^ 53 ≤ value (1.0 + x).toBits ∧
      FApprox (cOf x (1.0 + x) / (1.0 + x))
        ((1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits) (1 / 2 ^ 1075) := by
  set vx := value x.toBits with hvx
  have hdx : (2 : ℤ) ^ 1021 ∣ Wasm.IEEE64.scaledValue x.toBits := by
    apply scaled_dvd
    have := exponent_ge x.toBits 1022 (-1) (by norm_num) (by norm_num)
      (by rw [abs_of_neg (by linarith)]; norm_num; linarith)
    omega
  have hd1 : (2 : ℤ) ^ 1021 ∣ Wasm.IEEE64.scaledValue (1.0 : Float).toBits := by
    rw [one_scaled]
    exact pow_dvd_pow 2 (by norm_num)
  have hsx := scaled_of_value x.toBits vx rfl
  have hsum := F64ErrorTrack.add_exact_grid (1.0 : Float).toBits x.toBits one_float.1 hx 1021
    (by norm_num) hd1 hdx (by
      rw [one_scaled]
      have h3 : |((2 ^ 1074 + Wasm.IEEE64.scaledValue x.toBits : ℤ) : ℝ)| ≤ 2 ^ 53 * 2 ^ 1021 := by
        push_cast
        rw [hsx, abs_le]
        constructor <;> nlinarith
      exact_mod_cast h3)
  rw [one_float.2] at hsum
  have hu : (1.0 + x).toBits = Wasm.IEEE64.add (1.0 : Float).toBits x.toBits := F64Bits.toBits_add _ _
  rw [← hu] at hsum
  set vu := value (1.0 + x).toBits with hvu
  have hvu0 : 0 < vu := by rw [hsum.2]; linarith
  have hgrid : 1 / 2 ^ 53 ≤ vu := by
    obtain ⟨q, hq⟩ := hdx
    have h3 : vx * 2 ^ 1074 = 2 ^ 1021 * (q : ℝ) := by
      rw [← hsx]
      exact_mod_cast hq
    have h4 : -2 ^ 53 < (q : ℝ) := by nlinarith
    have h5 : (-2 ^ 53 : ℤ) < q := by exact_mod_cast h4
    have h6 : (-2 ^ 53 + 1 : ℝ) ≤ q := by exact_mod_cast (show (-2 ^ 53 + 1 : ℤ) ≤ q by omega)
    rw [hsum.2]
    nlinarith
  refine ⟨hsum.1, hsum.2, hgrid, ?_⟩
  have hc : cOf x (1.0 + x) = x - ((1.0 + x) - 1.0) := by
    unfold cOf
    rw [(k_cases (1.0 + x) hsum.1 hvu0).1 (by rw [← hvu, hsum.2]; linarith)]
    rfl
  rw [hc]
  -- `u - 1 = x`
  have hsu := scaled_of_value (1.0 + x).toBits (1 + vx) hsum.2
  have hdu : (2 : ℤ) ^ 1021 ∣ Wasm.IEEE64.scaledValue (1.0 + x).toBits := by
    have : Wasm.IEEE64.scaledValue (1.0 + x).toBits =
        2 ^ 1074 + Wasm.IEEE64.scaledValue x.toBits := by
      have h3 : ((Wasm.IEEE64.scaledValue (1.0 + x).toBits : ℤ) : ℝ) =
          ((2 ^ 1074 + Wasm.IEEE64.scaledValue x.toBits : ℤ) : ℝ) := by
        push_cast
        rw [hsu, hsx]
        ring
      exact_mod_cast h3
    rw [this]
    exact dvd_add (pow_dvd_pow 2 (by norm_num)) hdx
  have hdiff := F64ErrorTrack.sub_exact_grid (1.0 + x).toBits (1.0 : Float).toBits hsum.1
    one_float.1 1021 (by norm_num) hdu hd1 (by
      rw [one_scaled]
      have h3 : |((Wasm.IEEE64.scaledValue (1.0 + x).toBits - 2 ^ 1074 : ℤ) : ℝ)| ≤
          2 ^ 53 * 2 ^ 1021 := by
        push_cast
        rw [hsu, abs_le]
        constructor <;> nlinarith
      exact_mod_cast h3)
  rw [← F64Bits.toBits_sub, ← hvu, hsum.2, one_float.2] at hdiff
  have hm1 : FApprox ((1.0 + x) - 1.0) vx 0 :=
    ⟨hdiff.1, by rw [hdiff.2, ← hvx]; simp⟩
  have hcr := fapprox_sub (approx_self x.toBits hx) hm1 0 (by rw [← hvx]; simp) (by norm_num)
  have hdv := fapprox_div hcr ⟨hsum.1, by rw [← hvu, sub_self, abs_zero]⟩ 0 vu
    (by rw [← hvx]; simp)
    (le_abs_self vu) hvu0 0 (by simp) (by norm_num)
  refine Approx.congr (Approx.mono hdv (by simp)) ?_
  rw [hsum.2, ← hvx]
  ring

/-- `u = 1 + x` rounded once, as a rounded word and within `2 ^ -53` of `1 + x` relatively. -/
theorem sum_facts (x : Float) (hx : Finite x.toBits) (h1 : -1 < value x.toBits)
    (h2 : value x.toBits < 2 ^ 1000) :
    Rounded (1.0 + x).toBits (1 + value x.toBits) ∧
      |value (1.0 + x).toBits - (1 + value x.toBits)| ≤ (1 + value x.toBits) / 2 ^ 53 := by
  rw [F64Bits.toBits_add]
  have hR := add_rounded _ _ one_float.1 hx
    (by rw [one_float.2]; exact (by linarith : (0 : ℝ) < 1 + value x.toBits).ne')
    (by rw [one_float.2, abs_of_pos (by linarith)]; linarith [(by norm_num : (2 : ℝ) ^ 1000 + 1 < 2 ^ 1023)])
  rw [one_float.2] at hR
  refine ⟨hR, ?_⟩
  have h := F64AddBounds.add_real_relative _ _ one_float.1 hx (by
    rw [one_float.2, abs_of_pos (by linarith)]
    linarith [(by norm_num : (2 : ℝ) ^ 1000 + 1 < 2 ^ 1023)])
  rw [one_float.2, abs_of_pos (by linarith : (0 : ℝ) < 1 + value x.toBits)] at h
  have hu : unitRoundoff64 = 1 / 2 ^ 53 := rfl
  rw [hu] at h
  have := h.2
  rw [div_eq_mul_one_div (1 + value x.toBits), mul_comm]
  exact this

/-- `u` within `[1/2, 2]` and `c = x - (u - 1)`: `u - 1` is exact and `x - (u - 1)` rounds the
small value `1 + x - u`. -/
theorem corr_sterbenz (x : Float) (hx : Finite x.toBits) (hx1 : -1 < value x.toBits)
    (hk : (kOf (1.0 + x) >>> 63 == 0 && kOf (1.0 + x) != 0) = false) (mb : ℝ) (hmb : 1 / 2 ≤ mb)
    (hu1 : mb ≤ value (1.0 + x).toBits) (hu2 : value (1.0 + x).toBits ≤ 2)
    (hu : Finite (1.0 + x).toBits) (hx2 : 1 + value x.toBits ≤ 2)
    (herr : |value (1.0 + x).toBits - (1 + value x.toBits)| ≤ (1 + value x.toBits) / 2 ^ 53) :
    FApprox (cOf x (1.0 + x) / (1.0 + x))
      ((1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits) (1 / 2 ^ 60) ∧
      |(1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits| ≤ 1 / 2 ^ 52 := by
  set vx := value x.toBits with hvx
  set vu := value (1.0 + x).toBits with hvu
  have hc : cOf x (1.0 + x) = x - ((1.0 + x) - 1.0) := by
    unfold cOf
    rw [hk]
    rfl
  rw [hc]
  have hm1 : FApprox ((1.0 + x) - 1.0) (vu - 1) 0 := by
    unfold FApprox
    rw [F64Bits.toBits_sub]
    have h := F64Exact.sub_exact (1.0 + x).toBits (1.0 : Float).toBits hu one_float.1
      (by linarith) (by rw [one_float.2]; norm_num) (by rw [one_float.2]; linarith)
      (by rw [one_float.2]; linarith) (by linarith [(by norm_num : (2 : ℝ) < 2 ^ 900)])
      (by rw [one_float.2]; norm_num)
    rw [one_float.2] at h
    exact ⟨h.1, by rw [h.2, ← hvu, sub_self, abs_zero]⟩
  have he := abs_le.mp herr
  have he_l := he.1
  have he_r := he.2
  have h3 : (1 + vx) * (1 - 1 / 2 ^ 53) ≤ vu := by linarith
  have h4 : 1 + vx ≤ 2 * vu := by nlinarith
  have hd : |vx - (vu - 1)| ≤ 1 / 2 ^ 52 := by
    rw [show vx - (vu - 1) = -(vu - (1 + vx)) by ring, abs_neg]
    refine herr.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith
  have hcr := fapprox_sub (approx_self x.toBits hx) hm1 (1 / 2 ^ 52) (by linarith) (by norm_num)
  have hvu0 : 0 < vu := by linarith
  have hdv := fapprox_div hcr ⟨hu, by rw [sub_self, abs_zero]⟩ (1 / 2 ^ 52) mb hd
    (by rw [abs_of_pos hvu0]; exact hu1) (by linarith) (1 / 2 ^ 50) (by
      rw [div_le_iff₀ (by linarith)]
      norm_num
      nlinarith) (by norm_num)
  refine ⟨Approx.congr (Approx.mono hdv ?_) (by ring), ?_⟩
  · have h1 : (0 + 0 + 1 / 2 ^ 52 / 2 ^ 53 + 1 / 2 ^ 52 * 0 / mb) / (mb - 0) ≤ 1 / 2 ^ 104 := by
      rw [div_le_iff₀ (by linarith)]
      norm_num
      nlinarith
    have h2 : (1 : ℝ) / 2 ^ 104 + 1 / 2 ^ 50 / 2 ^ 53 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 60 := by norm_num
    linarith
  · rw [abs_div, abs_of_pos hvu0, div_le_iff₀ hvu0]
    rw [show 1 + vx - vu = -(vu - (1 + vx)) by ring, abs_neg]
    refine herr.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- A rounded word of `S` is at least `S - d` when a word of value `S - d ≥ 0` exists. -/
theorem rounded_lower (c v : UInt64) (S d : ℝ) (hc : Rounded c S) (hS : 0 < S) (hd : 0 ≤ d)
    (hv : value v = S - d) (hv0 : 0 ≤ S - d) : S - d ≤ |value c| := by
  have h := hc.2.2.2 v
  rw [hv, abs_of_nonneg hv0, abs_of_pos hS, show S - d - S = -d by ring, abs_neg,
    abs_of_nonneg hd] at h
  obtain ⟨hab_l, hab_r⟩ := abs_le.mp h
  linarith

/-- `-1/2 < x ≤ -1228485/2^22`: `u` in `[1/2, 1482910/2^21)`, below the threshold of the
reduction. -/
theorem corr_mid (x : Float) (hx : Finite x.toBits) (h1 : -1 / 2 < value x.toBits)
    (h2 : value x.toBits ≤ -1228485 / 4194304) :
    Finite (1.0 + x).toBits ∧ 1 / 2 ≤ value (1.0 + x).toBits ∧
      value (1.0 + x).toBits < 1482910 / 2097152 ∧
      FApprox (cOf x (1.0 + x) / (1.0 + x))
        ((1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits) (1 / 2 ^ 60) ∧
      |(1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits| ≤ 1 / 2 ^ 52 := by
  obtain ⟨hR, herr⟩ := sum_facts x hx (by linarith) (by linarith [(by norm_num : (0 : ℝ) < 2 ^ 1000)])
  have hB : value (UInt64.ofNat (1022 * 2 ^ 52)) = 1 / 2 := by
    rw [F64PositiveSpacing.boundary_value 1022 (by norm_num) (by norm_num)]
    norm_num
  have hlo := rounded_ge _ _ hR 1022 (by norm_num) (by norm_num) (by rw [hB]; linarith)
  rw [hB] at hlo
  have he := abs_le.mp herr
  have he_l := he.1
  have he_r := he.2
  have hhi : value (1.0 + x).toBits < 1482910 / 2097152 := by
    have : (1 + value x.toBits) / 2 ^ 53 ≤ 1 / 2 ^ 53 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    have h3 : (1 : ℝ) - 1228485 / 4194304 + 1 / 2 ^ 53 < 1482910 / 2097152 := by norm_num
    linarith
  have hk := (k_cases (1.0 + x) hR.1 (by linarith)).1 (by linarith)
  obtain ⟨hc, ht⟩ := corr_sterbenz x hx (by linarith) hk (1 / 2) le_rfl hlo (by linarith) hR.1
    (by linarith) herr
  exact ⟨hR.1, hlo, hhi, hc, ht⟩

/-- `0.4142 ≤ x ≤ 1 - 2 ^ -52`: `u` in `[1.4142132, 2)`. -/
theorem corr_hi (x : Float) (hx : Finite x.toBits) (h1 : 41421365 / 10 ^ 8 ≤ value x.toBits)
    (h2 : value x.toBits ≤ 1 - 1 / 2 ^ 52) :
    Finite (1.0 + x).toBits ∧ 14142132 / 10 ^ 7 ≤ value (1.0 + x).toBits ∧
      value (1.0 + x).toBits < 2 ∧
      FApprox (cOf x (1.0 + x) / (1.0 + x))
        ((1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits) (1 / 2 ^ 60) ∧
      |(1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits| ≤ 1 / 2 ^ 52 := by
  obtain ⟨hR, herr⟩ := sum_facts x hx (by linarith) (by linarith [(by norm_num : (2 : ℝ) < 2 ^ 1000)])
  have he := abs_le.mp herr
  have he_l := he.1
  have he_r := he.2
  have hlo : 14142132 / 10 ^ 7 ≤ value (1.0 + x).toBits := by
    norm_num at he h1 ⊢
    linarith
  have hlt : value (1.0 + x).toBits < 2 := by
    norm_num at he h2 ⊢
    linarith
  have hk := (k_cases (1.0 + x) hR.1 (by linarith)).2.1 (by linarith) hlt
  obtain ⟨hc, ht⟩ := corr_sterbenz x hx (by linarith) hk (1 / 2) le_rfl (by linarith)
    hlt.le hR.1 (by linarith) herr
  exact ⟨hR.1, hlo, hlt, hc, ht⟩

/-- `1 ≤ x < 2 ^ 53`: `u - x` and `1 - (u - x)` are exact on the grid of `x`. -/
theorem corr_big (x : Float) (hx : Finite x.toBits) (h1 : 1 ≤ value x.toBits)
    (h2 : value x.toBits < 2 ^ 53) :
    Finite (1.0 + x).toBits ∧ 2 ≤ value (1.0 + x).toBits ∧
      value (1.0 + x).toBits ≤ 2 ^ 54 ∧
      FApprox (cOf x (1.0 + x) / (1.0 + x))
        ((1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits) (1 / 2 ^ 60) ∧
      |(1 + value x.toBits - value (1.0 + x).toBits) / value (1.0 + x).toBits| ≤ 1 / 2 ^ 52 := by
  set vx := value x.toBits with hvx
  obtain ⟨hR, herr⟩ := sum_facts x hx (by linarith) (by linarith [(by norm_num : (2 : ℝ) ^ 53 < 2 ^ 1000)])
  set u := 1.0 + x with hudef
  set vu := value u.toBits with hvu
  have hu := hR.1
  have he := abs_le.mp herr
  have he_l := he.1
  have he_r := he.2
  -- `u ≥ x`, so the exponent field of `u` is at least that of `x`
  have hvu0 : 0 < vu := by
    have : (1 + vx) / 2 ^ 53 ≤ (1 + vx) / 2 := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num) (by norm_num)
    linarith
  have hxu : vx ≤ vu := by
    have := rounded_lower u.toBits x.toBits (1 + vx) 1 hR (by linarith) (by norm_num)
      (by ring) (by linarith)
    rw [abs_of_pos hvu0] at this
    linarith
  have hx63 := pos_word x.toBits (by linarith)
  have hu63 := pos_word u.toBits hvu0
  have hle : x.toBits.toNat ≤ u.toBits.toNat :=
    (F64PositiveOrder.value_le_iff hx63 hu63).mp hxu
  have hex : Wasm.IEEE64.exponent x.toBits = x.toBits.toNat / 2 ^ 52 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have heu : Wasm.IEEE64.exponent u.toBits = u.toBits.toNat / 2 ^ 52 := by
    simp only [Wasm.IEEE64.exponent]
    omega
  have hx1023 : 1023 ≤ Wasm.IEEE64.exponent x.toBits :=
    exponent_ge x.toBits 1023 0 (by norm_num) (by norm_num) (by rw [abs_of_pos (by linarith)]; simpa using h1)
  have hx1075 : Wasm.IEEE64.exponent x.toBits ≤ 1075 := by
    by_contra hc
    have := F64Magnitude.magnitude_ge x.toBits 1076 53 (by norm_num) (by norm_num) (by norm_num)
      (by omega)
    rw [abs_of_pos (by linarith)] at this
    norm_num at this
    linarith
  set s := Wasm.IEEE64.exponent x.toBits - 1 with hs
  have hdx : (2 : ℤ) ^ s ∣ Wasm.IEEE64.scaledValue x.toBits := scaled_dvd _ s le_rfl
  have hdu : (2 : ℤ) ^ s ∣ Wasm.IEEE64.scaledValue u.toBits := scaled_dvd _ s (by omega)
  have hd1 : (2 : ℤ) ^ s ∣ Wasm.IEEE64.scaledValue (1.0 : Float).toBits := by
    rw [one_scaled]
    exact pow_dvd_pow 2 (by omega)
  -- the scale of the grid
  obtain ⟨M, hM, hMx⟩ := F64Exact.magnitude_grid x.toBits
  have hsx : Wasm.IEEE64.scaledValue x.toBits = (M : ℤ) * 2 ^ s := by
    have hsg : Wasm.IEEE64.sign x.toBits = false := by
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
      exact hx63
    simp only [Wasm.IEEE64.scaledValue, hsg, Bool.false_eq_true, ite_false, hMx]
    push_cast
    ring
  have hxs : vx * 2 ^ 1074 < 2 ^ 53 * 2 ^ s := by
    have h3 := scaled_of_value x.toBits vx rfl
    rw [hsx] at h3
    push_cast at h3
    rw [← h3]
    have : (M : ℝ) < 2 ^ 53 := by exact_mod_cast hM
    have hp : (0 : ℝ) < 2 ^ s := by positivity
    nlinarith
  have hs1022 : (2 : ℝ) ^ 1022 ≤ 2 ^ s := pow_le_pow_right₀ (by norm_num) (by omega)
  have hsu := scaled_of_value u.toBits vu rfl
  have hsx' := scaled_of_value x.toBits vx rfl
  -- `u - x` is exact
  have hux := F64ErrorTrack.sub_exact_grid u.toBits x.toBits hu hx s (by omega) hdu hdx (by
    have h3 : |((Wasm.IEEE64.scaledValue u.toBits - Wasm.IEEE64.scaledValue x.toBits : ℤ) : ℝ)| ≤
        2 ^ 53 * 2 ^ s := by
      push_cast
      rw [hsu, hsx', ← sub_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ vu - vx)]
      have h7 : vu - vx ≤ 1 + (1 + vx) / 2 ^ 53 := by linarith
      have h8 : vx * 2 ^ 1021 < 2 ^ s := by
        have h9 := hxs
        rw [show vx * (2 : ℝ) ^ 1074 = vx * 2 ^ 1021 * 2 ^ 53 by ring,
          mul_comm ((2 : ℝ) ^ 53)] at h9
        exact lt_of_mul_lt_mul_right h9 (by positivity)
      calc (vu - vx) * 2 ^ 1074 ≤ (1 + (1 + vx) / 2 ^ 53) * 2 ^ 1074 :=
            mul_le_mul_of_nonneg_right h7 (by positivity)
        _ = 2 ^ 1074 + 2 ^ 1021 + vx * 2 ^ 1021 := by ring
        _ ≤ 2 ^ 53 * 2 ^ s := by linarith
    exact_mod_cast h3)
  rw [← F64Bits.toBits_sub] at hux
  set d := u - x with hd
  have hsd := scaled_of_value d.toBits (vu - vx) hux.2
  have hdd : (2 : ℤ) ^ s ∣ Wasm.IEEE64.scaledValue d.toBits := by
    have : Wasm.IEEE64.scaledValue d.toBits =
        Wasm.IEEE64.scaledValue u.toBits - Wasm.IEEE64.scaledValue x.toBits := by
      have h3 : ((Wasm.IEEE64.scaledValue d.toBits : ℤ) : ℝ) =
          ((Wasm.IEEE64.scaledValue u.toBits - Wasm.IEEE64.scaledValue x.toBits : ℤ) : ℝ) := by
        push_cast
        rw [hsd, hsu, hsx']
        ring
      exact_mod_cast h3
    rw [this]
    exact dvd_sub hdu hdx
  -- `1 - (u - x)` is exact
  have h1d := F64ErrorTrack.sub_exact_grid (1.0 : Float).toBits d.toBits one_float.1 hux.1 s
    (by omega) hd1 hdd (by
      rw [one_scaled]
      have h3 : |((2 ^ 1074 - Wasm.IEEE64.scaledValue d.toBits : ℤ) : ℝ)| ≤ 2 ^ 53 * 2 ^ s := by
        push_cast
        rw [hsd, abs_le]
        constructor <;> nlinarith
      exact_mod_cast h3)
  rw [← F64Bits.toBits_sub, one_float.2, hux.2] at h1d
  have hvu2 : 2 ≤ vu := by
    have hB : value (UInt64.ofNat (1024 * 2 ^ 52)) = 2 := by
      rw [F64PositiveSpacing.boundary_value 1024 (by norm_num) (by norm_num)]
      norm_num
    have := rounded_ge _ _ hR 1024 (by norm_num) (by norm_num) (by rw [hB]; linarith)
    rw [hB] at this
    exact this
  have hk := (k_cases u hu hvu0).2.2 hvu2
  have hc : cOf x u = 1.0 - (u - x) := by
    unfold cOf
    rw [hk]
    rfl
  have hcr : FApprox (1.0 - (u - x)) (1 + vx - vu) 0 :=
    ⟨h1d.1, by rw [h1d.2, ← hvu, ← hvx, show (1 : ℝ) - (vu - vx) - (1 + vx - vu) = 0 by ring,
      abs_zero]⟩
  have hmb : (1 + vx) * (1 - 1 / 2 ^ 53) ≤ vu := by linarith
  have herr' : |1 + vx - vu| ≤ (1 + vx) / 2 ^ 53 := by
    rw [show 1 + vx - vu = -(vu - (1 + vx)) by ring, abs_neg]
    exact herr
  have hdv := fapprox_div hcr ⟨hu, by rw [sub_self, abs_zero]⟩ ((1 + vx) / 2 ^ 53)
    ((1 + vx) * (1 - 1 / 2 ^ 53)) herr' (by rw [abs_of_pos hvu0]; exact hmb) (by nlinarith)
    (1 / 2 ^ 52) (by
        rw [div_le_iff₀ (by nlinarith)]
        field_simp
        nlinarith) (by norm_num)
  rw [hc]
  refine ⟨hu, hvu2, by linarith, Approx.mono hdv ?_, ?_⟩
  · have h3 : (0 + (1 + vx) / 2 ^ 53 * 0 / ((1 + vx) * (1 - 1 / 2 ^ 53))) /
        ((1 + vx) * (1 - 1 / 2 ^ 53) - 0) = 0 := by simp
    rw [h3]
    norm_num
  · rw [abs_div, abs_of_pos hvu0, div_le_iff₀ hvu0,
      show 1 + vx - vu = -(vu - (1 + vx)) by ring, abs_neg]
    refine herr.trans ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith

end Library.Numerics.Float64.Log1p.Log1pTheoremCorr
