import Library.Numerics.Float64.Asinh.AtanhTheoremBranches
import Library.Numerics.Float64.Asinh.AsinhTheoremCompose
import Library.Numerics.Float64.Asinh.AsinhTheoremMid
import Mathlib.Analysis.SpecialFunctions.Artanh

/-!
`Asinh.atanh` below `1/2`: the code returns `0.5 log1p w` with `w = 2a + 2a·a/(1 - a)` for
`a = |x|`.  `2a` is exact and `q = 2a·a/(1 - a)` has relative error below `3.0001 · 2 ^ -53`
(`atanh_q`).  `Library.Numerics.Float64.Log1p.Log1pTheoremNear.log1p_near` bounds the exact value of `log1p`'s last operation
against `log (1 + w)`, `AsinhTheoremCompose.near_compose` moves the bound to
`log (1 + W) = 2 artanh a` with `W = 2a/(1 - a)`, and `F64Near.Near.half` halves it.  Below
`a = 0.1244` the bound is relative (`atanh_piece_rel`); above it each input range has a constant
bound against two spacings of the binade of `artanh a` (`atanh_piece`).
-/

namespace Library.Numerics.Float64.Asinh.AtanhTheoremSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RelError F64Near F64HalfUlp Library.Numerics.Float64.Log1p.Log1pTheoremNear
  AsinhTheoremCompose AsinhTheoremMid

set_option exponentiation.threshold 4096

/-- `t = 2a` is exact, and `q = t a/(1 - a)` has relative error below `3.0001 · 2 ^ -53`. -/
theorem atanh_q (a : Float) (ha : Finite a.toBits) (h28 : 1 / 2 ^ 28 ≤ value a.toBits)
    (h5 : value a.toBits ≤ 1 / 2) :
    RApprox (a + a).toBits (2 * value a.toBits) 0 ∧
      RApprox ((a + a) * a / (1.0 - a)).toBits
        (2 * value a.toBits * value a.toBits / (1 - value a.toBits)) (30001 / 10000 / 2 ^ 53) := by
  set va := value a.toBits with hva
  have hv0 : 0 < va := lt_of_lt_of_le (by positivity) h28
  obtain ⟨htf, htv⟩ := add_self_exact a ha
    (by rw [abs_of_pos hv0]; linarith [(by norm_num : (1 : ℝ) / 2 ^ 1000 ≤ 1 / 2 ^ 28)])
    (by rw [abs_of_pos hv0]; linarith [(by norm_num : (1 : ℝ) / 2 < 2 ^ 900)])
  have hT : RApprox (a + a).toBits (2 * va) 0 := by
    have h := rapprox_self _ htf (by rw [htv]; linarith)
    rwa [htv] at h
  have hA : RApprox a.toBits va 0 := rapprox_self _ ha hv0
  have hsq : 1 / 2 ^ 56 ≤ va * va := by
    have := mul_le_mul h28 h28 (by positivity) hv0.le
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 28 * (1 / 2 ^ 28) = 1 / 2 ^ 56)]
  have hm := rapprox_mul hT hA (1 / 2 ^ 1000)
    (by nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 56))])
    (by nlinarith)
  rw [← F64Bits.toBits_mul] at hm
  have hd := rapprox_sub one_rapprox hA (by linarith) 0 (by simp) (by nlinarith)
  rw [← F64Bits.toBits_sub] at hd
  have hq := rapprox_div hm hd (by norm_num) (1 / 2 ^ 1000)
    (by
      have h1 : va * va ≤ 2 * va * va / (1 - va) := by
        rw [le_div_iff₀ (by linarith)]
        nlinarith
      nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 56))])
    (by
      have h1 : 2 * va * va / (1 - va) ≤ 1 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have h2 : (1 + (0 + 0 + 0 * 0 + (1 + 0) * (1 + 0) / 2 ^ 53 + 1 / 2 ^ 1000)) /
          (1 - (0 + (1 + 0) / 2 ^ 53)) ≤ (2 : ℝ) := by norm_num
      nlinarith)
  rw [← F64Bits.toBits_div] at hq
  exact ⟨hT, hq.mono (by norm_num)⟩

theorem two_artanh (va : ℝ) (h0 : 0 ≤ va) (h1 : va < 1) :
    2 * Real.artanh va = Real.log (1 + va) - Real.log (1 - va) := by
  rw [Real.artanh_eq_half_log ⟨by linarith, h1.le⟩,
    Real.log_div (by linarith : (0 : ℝ) < 1 + va).ne' (by linarith : (0 : ℝ) < 1 - va).ne']
  ring

theorem log_W (va : ℝ) (h0 : 0 ≤ va) (h1 : va < 1) :
    Real.log (1 + 2 * va / (1 - va)) = Real.log (1 + va) - Real.log (1 - va) := by
  have hd : 0 < 1 - va := by linarith
  rw [← Real.log_div (x := 1 + va) (y := 1 - va) (by linarith : (0 : ℝ) < 1 + va).ne' hd.ne']
  congr 1
  field_simp
  ring

/-- A range `[aL, aH]` of `a` with a constant bound `E` of `log1p` and `K` of the argument
term, against two spacings of binade `n`. -/
theorem atanh_piece (a : Float) (ha : Finite a.toBits) (aL aH ρ h E K YL : ℝ) (g n : ℕ)
    (haL : aL ≤ value a.toBits) (haH : value a.toBits ≤ aH) (h28 : 1 / 2 ^ 28 ≤ aL)
    (h5 : aH ≤ 1 / 2) (hg : g ≤ 1023) (hρ : 30001 / 10000 / 2 ^ 53 ≤ ρ) (hρ1 : ρ ≤ 1 / 2 ^ 50)
    (hh : 2 ^ g / 2 / 2 ^ 1074 ≤ h) (hh1 : h ≤ 1 / 2 ^ 52)
    (hgW : 2 * aH / (1 - aH) + ρ * (2 * aH * aH / (1 - aH)) < 2 ^ (53 + g) / 2 ^ 1074)
    (hE : ∀ v : ℝ, 2 * aL / (1 - aL) - (ρ * (2 * aH * aH / (1 - aH)) + h) ≤ v →
        v ≤ 2 * aH / (1 - aH) + (ρ * (2 * aH * aH / (1 - aH)) + h) → errBound v ≤ E)
    (hK0 : 0 ≤ K)
    (hK1 : 2 * ρ * (1 + K) * aL ^ 2 + (-h * (1 + K) - K) * aL + (h * (1 + K) - K) ≤ 0)
    (hK2 : 2 * ρ * (1 + K) * aH ^ 2 + (-h * (1 + K) - K) * aH + (h * (1 + K) - K) ≤ 0)
    (hYL : YL ≤ Real.log (1 + aL) - Real.log (1 - aL)) (hEK : E + K ≤ 1)
    (hY998 : 1 / 2 ^ 998 + (E + K) ≤ YL)
    (hn1 : 1 ≤ n) (hn : n < 2047)
    (hB : value (UInt64.ofNat (n * 2 ^ 52)) + (E + K) / 2 ≤ YL / 2)
    (hT : (E + K) / 2 < 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074)) :
    F64SignedRounding.WithinSteps 2 (Real.artanh (value a.toBits))
      (0.5 * Log1p.log1p (a + a + (a + a) * a / (1.0 - a))).toBits := by
  set va := value a.toBits with hva
  have hv0 : 0 < va := lt_of_lt_of_le (by positivity) (h28.trans haL)
  have hv1 : va ≤ 1 / 2 := haH.trans h5
  obtain ⟨hT2, hq⟩ := atanh_q a ha (h28.trans haL) hv1
  have hden : 0 < 1 - va := by linarith
  have hne : 1 - va ≠ 0 := hden.ne'
  have hdenH : 0 < 1 - aH := by linarith
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  have hh0 : 0 < h := lt_of_lt_of_le (by positivity) hh
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * va * va / (1 - va) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 2 * va / (1 - va) := ⟨_, rfl⟩
  rw [← hQ] at hq
  have hq' : FApprox ((a + a) * a / (1.0 - a)) Q (ρ * Q) := (hq.mono hρ).2
  have hWQ : 2 * va + Q = W := by
    rw [hQ, hW]
    field_simp
    ring
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hv0.le) hv0.le) hden.le
  have hQH : Q ≤ 2 * aH * aH / (1 - aH) := by
    rw [hQ]
    apply div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)) _ hdenH
      (by linarith)
    have := mul_le_mul haH haH hv0.le (by linarith)
    linarith
  have hQH1 : 2 * aH * aH / (1 - aH) ≤ 1 := by
    rw [div_le_iff₀ hdenH]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - 2 * aH) (by linarith : (0 : ℝ) ≤ aH + 1)
    linarith
  have hWH : W ≤ 2 * aH / (1 - aH) := by
    rw [hW]
    exact div_le_div₀ (by linarith) (by linarith) hdenH (by linarith)
  have hWL : 2 * aL / (1 - aL) ≤ W := by
    rw [hW]
    exact div_le_div₀ (by linarith) (by linarith) hden (by linarith)
  have hW2 : 2 * va ≤ W := by linarith
  -- the last addition
  have hw0 := fapprox_add_half hT2.2 hq' g hg (by
    rw [zero_mul, zero_add, abs_of_pos (by linarith : (0 : ℝ) < 2 * va + Q), hWQ]
    have : ρ * Q ≤ ρ * (2 * aH * aH / (1 - aH)) := mul_le_mul_of_nonneg_left hQH hρ0
    linarith)
  obtain ⟨w, hwdef⟩ : ∃ w : Float, w = a + a + (a + a) * a / (1.0 - a) := ⟨_, rfl⟩
  rw [← hwdef] at hw0
  rw [← hwdef]
  have hd : |value w.toBits - W| ≤ ρ * Q + h := by
    have := hw0.2
    rw [hWQ, zero_mul, zero_add] at this
    linarith
  have hda := abs_le.mp hd
  have hδH : ρ * Q + h ≤ ρ * (2 * aH * aH / (1 - aH)) + h := by
    linarith [mul_le_mul_of_nonneg_left hQH hρ0]
  have hδs : ρ * Q + h ≤ 1 / 2 ^ 40 := by
    have : ρ * (2 * aH * aH / (1 - aH)) ≤ ρ := mul_le_of_le_one_right hρ0 hQH1
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 + 1 / 2 ^ 52 ≤ 1 / 2 ^ 40)]
  have hw29 : 1 / 2 ^ 29 ≤ value w.toBits := by
    have : (1 : ℝ) / 2 ^ 29 + 1 / 2 ^ 40 ≤ 2 * (1 / 2 ^ 28) := by norm_num
    linarith [h28.trans haL]
  have hN := (log1p_near w hw0.1 hw29).mono (hE _ (by linarith) (by linarith))
  have hm : 0 < 1 + W - (ρ * Q + h) := by linarith
  have hN2 := near_compose hN hd hm (by linarith) (by linarith)
  have hKq := quad_le (2 * ρ * (1 + K)) (-h * (1 + K) - K) (h * (1 + K) - K) aL aH va
    (mul_nonneg (mul_nonneg (by norm_num) hρ0) (by linarith)) haL haH hK1 hK2
  have hδK : (ρ * Q + h) / (1 + W - (ρ * Q + h)) ≤ K := by
    rw [div_le_iff₀ hm]
    have e1 : (ρ * Q + h) * (1 - va) = 2 * ρ * va ^ 2 + h * (1 - va) := by
      rw [hQ]
      field_simp
    have e2 : (1 + W) * (1 - va) = 1 + va := by
      rw [hW]
      field_simp
      ring
    have e3 : (ρ * Q + h) * (1 - va) ≤ K * (1 + W - (ρ * Q + h)) * (1 - va) := by
      have : K * (1 + W - (ρ * Q + h)) * (1 - va) =
          K * ((1 + W) * (1 - va)) - K * ((ρ * Q + h) * (1 - va)) := by ring
      rw [this, e1, e2]
      linarith [hKq]
    exact le_of_mul_le_mul_right e3 hden
  have hLW : Real.log (1 + W) = 2 * Real.artanh va := by
    rw [two_artanh va hv0.le (by linarith), hW, log_W va hv0.le (by linarith)]
  have hN3 : Near (Log1p.log1p w).toBits (2 * Real.artanh va) (E + K) := by
    rw [← hLW]
    exact hN2.mono (by linarith)
  have hY : YL ≤ 2 * Real.artanh va := by
    rw [two_artanh va hv0.le (by linarith)]
    have h1 : Real.log (1 + aL) ≤ Real.log (1 + va) := Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (1 - va) ≤ Real.log (1 - aL) := Real.log_le_log hden (by linarith)
    linarith
  have hYu : 2 * Real.artanh va ≤ 2 := by
    rw [← hLW]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + W)
    have h2 : 2 * aH / (1 - aH) ≤ 2 := by
      rw [div_le_iff₀ hdenH]
      linarith
    linarith
  have hY0 : 0 ≤ 2 * Real.artanh va := by
    rw [← hLW]
    exact Real.log_nonneg (by linarith)
  have hN4 := hN3.half (by rw [abs_of_nonneg hY0]; linarith)
    (by rw [abs_of_nonneg hY0]; linarith [(by norm_num : (3 : ℝ) < 2 ^ 1000)])
  rw [show 2 * Real.artanh va / 2 = Real.artanh va by ring] at hN4
  rw [F64Bits.toBits_mul, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
  refine hN4.within_two n hn1 hn ?_ hT ?_
  · rw [abs_of_nonneg (by linarith)]
    generalize value (UInt64.ofNat (n * 2 ^ 52)) = B at hB ⊢
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith [(by norm_num : (1 : ℝ) < 2 ^ 1023)]

/-- A range `[aL, aH]` below `a = 1/8` with a bound relative to `artanh a`. -/
theorem atanh_piece_rel (a : Float) (ha : Finite a.toBits) (aL aH ρ WL WH ρw ρt : ℝ)
    (haL : aL ≤ value a.toBits) (haH : value a.toBits ≤ aH) (h28 : 1 / 2 ^ 28 ≤ aL)
    (h8 : aH ≤ 1 / 8) (hρ : 30001 / 10000 / 2 ^ 53 ≤ ρ) (hWL : WL ≤ 2 * aL / (1 - aL))
    (hWL0 : 0 ≤ WL) (hWH : 2 * aH / (1 - aH) ≤ WH)
    (hρw : ρ * aH + (1 + ρ * aH) / 2 ^ 53 ≤ ρw)
    (hρw1 : ρw ≤ 1 / 2 ^ 50) (hWH1 : WH * (1 + ρw) ≤ 285 / 1000)
    (hρt : (1 + ρw) * (174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59) +
      ρw / (1 + WL * (1 - ρw)) ≤ ρt * (1 - aH))
    (hρt1 : ρt * (2 ^ 52 + 1) < 1) :
    F64SignedRounding.WithinSteps 2 (Real.artanh (value a.toBits))
      (0.5 * Log1p.log1p (a + a + (a + a) * a / (1.0 - a))).toBits := by
  set va := value a.toBits with hva
  have hv0 : 0 < va := lt_of_lt_of_le (by positivity) (h28.trans haL)
  have hv1 : va ≤ 1 / 8 := haH.trans h8
  obtain ⟨hT2, hq⟩ := atanh_q a ha (h28.trans haL) (by linarith)
  have hden : 0 < 1 - va := by linarith
  have hne : 1 - va ≠ 0 := hden.ne'
  have hdenH : 0 < 1 - aH := by linarith
  have hρ0 : 0 ≤ ρ := le_trans (by positivity) hρ
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = 2 * va * va / (1 - va) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = 2 * va / (1 - va) := ⟨_, rfl⟩
  rw [← hQ] at hq
  have hq' := hq.mono hρ
  have hWQ : 2 * va + Q = W := by
    rw [hQ, hW]
    field_simp
    ring
  have hQW : Q = va * W := by
    rw [hQ, hW]
    field_simp
  have hW0 : 0 < W := by
    rw [hW]
    exact div_pos (by linarith) hden
  have hWH' : W ≤ WH := by
    rw [hW]
    exact (div_le_div₀ (by linarith) (by linarith) hdenH (by linarith)).trans hWH
  have hWL' : WL ≤ W := by
    rw [hW]
    exact hWL.trans (div_le_div₀ (by linarith) (by linarith) hden (by linarith))
  have hW2 : 2 * va ≤ W := by linarith [hWQ, hQW, mul_nonneg hv0.le hW0.le]
  have hWH0 : 0 ≤ WH := le_trans hW0.le hWH'
  have haH0 : 0 ≤ aH := by linarith
  have hρw0 : 0 ≤ ρw := le_trans (add_nonneg (mul_nonneg hρ0 haH0)
    (div_nonneg (by linarith [mul_nonneg hρ0 haH0]) (by positivity))) hρw
  -- the last addition, relative
  have hwR := (rapprox_add hT2 hq' (ρ * aH) (by
    rw [zero_mul, zero_add, hWQ, hQW]
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right haH hW0.le) hρ0
    linarith) (by
      rw [hWQ]
      have h1 : ρ * aH ≤ 1 := by
        have : (0 : ℝ) ≤ (1 + ρ * aH) / 2 ^ 53 := div_nonneg (by linarith [mul_nonneg hρ0 haH0])
          (by positivity)
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 ≤ 1)]
      have h2 : W ≤ 1 := by linarith [mul_nonneg hWH0 hρw0]
      have := mul_le_mul (by linarith : 1 + ρ * aH ≤ 2) h2 hW0.le (by norm_num)
      linarith [(by norm_num : (2 : ℝ) * 1 < 2 ^ 1023)])).mono hρw
  rw [← F64Bits.toBits_add, hWQ] at hwR
  obtain ⟨w, hwdef⟩ : ∃ w : Float, w = a + a + (a + a) * a / (1.0 - a) := ⟨_, rfl⟩
  rw [← hwdef] at hwR
  rw [← hwdef]
  have hd : |value w.toBits - W| ≤ ρw * W := hwR.2.2
  have hda := abs_le.mp hd
  have hρwh : ρw ≤ 1 / 2 := hρw1.trans (by norm_num)
  have hρwW : ρw * W ≤ W / 2 := by
    have := mul_le_mul_of_nonneg_right hρwh hW0.le
    linarith
  have hw29 : 1 / 2 ^ 29 ≤ value w.toBits := by
    have h1 : 2 * (1 / 2 ^ 28) ≤ W := by linarith [h28.trans haL]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 29 ≤ 2 * (1 / 2 ^ 28) / 2)]
  have hwu : value w.toBits ≤ W * (1 + ρw) := by linarith [hda.2]
  have hw285 : value w.toBits ≤ 285 / 1000 := by
    have := mul_le_mul_of_nonneg_right hWH' (by linarith : (0 : ℝ) ≤ 1 + ρw)
    linarith
  have hEb : errBound (value w.toBits) =
      174 / 100 / 2 ^ 53 * value w.toBits ^ 2 + value w.toBits / 2 ^ 59 := by
    rw [errBound, ite_eq_left hw285]
  have hN := log1p_near w hwR.2.1 hw29
  rw [hEb] at hN
  have hW1 : 0 ≤ W * (1 - ρw) := mul_nonneg hW0.le (by linarith)
  have hm : 0 < 1 + W * (1 - ρw) := by linarith
  have hN2 := near_compose hN hd hm (by linarith [hda.1]) (by linarith [mul_nonneg hρw0 hW0.le])
  have hvw0 : 0 ≤ value w.toBits := by linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 29)]
  have hC0 : 0 ≤ 174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59 :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hWH0 (by linarith))) (by norm_num)
  have hE1 : 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 + value w.toBits / 2 ^ 59 ≤
      W * ((1 + ρw) * (174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59)) := by
    have h1 : value w.toBits ≤ WH * (1 + ρw) := by
      have := mul_le_mul_of_nonneg_right hWH' (by linarith : (0 : ℝ) ≤ 1 + ρw)
      linarith
    have h2 : 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 ≤
        174 / 100 / 2 ^ 53 * (value w.toBits * (WH * (1 + ρw))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [sq]
      exact mul_le_mul_of_nonneg_left h1 hvw0
    have h3 : value w.toBits * (174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59) ≤
        W * (1 + ρw) * (174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59) :=
      mul_le_mul_of_nonneg_right hwu hC0
    calc 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 + value w.toBits / 2 ^ 59
        ≤ 174 / 100 / 2 ^ 53 * (value w.toBits * (WH * (1 + ρw))) + value w.toBits / 2 ^ 59 := by
          linarith
      _ = value w.toBits * (174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59) := by ring
      _ ≤ W * (1 + ρw) * (174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59) := h3
      _ = _ := by ring
  have hm2 : 0 < 1 + WL * (1 - ρw) := by
    have := mul_nonneg hWL0 (by linarith : (0 : ℝ) ≤ 1 - ρw)
    linarith
  have hE2 : ρw * W / (1 + W * (1 - ρw)) ≤ W * (ρw / (1 + WL * (1 - ρw))) := by
    rw [mul_div_assoc', div_le_div_iff₀ hm hm2]
    have : WL * (1 - ρw) ≤ W * (1 - ρw) := mul_le_mul_of_nonneg_right hWL' (by linarith)
    have h4 := mul_le_mul_of_nonneg_left this (mul_nonneg hρw0 hW0.le)
    calc ρw * W * (1 + WL * (1 - ρw)) = ρw * W + ρw * W * (WL * (1 - ρw)) := by ring
      _ ≤ ρw * W + ρw * W * (W * (1 - ρw)) := by linarith
      _ = W * ρw * (1 + W * (1 - ρw)) := by ring
  have hLW : Real.log (1 + W) = 2 * Real.artanh va := by
    rw [two_artanh va hv0.le (by linarith), hW, log_W va hv0.le (by linarith)]
  have hart : 2 * va ≤ 2 * Real.artanh va := by
    rw [← hLW]
    have h1 := log_pade W hW0
    have h2 : 2 * W / (2 + W) = 2 * va := by
      rw [hW]
      field_simp
      ring
    linarith
  have hWa : W * (1 - aH) ≤ 2 * va := by
    have : W * (1 - va) = 2 * va := by
      rw [hW]
      field_simp
    have := mul_le_mul_of_nonneg_left (by linarith : 1 - aH ≤ 1 - va) hW0.le
    linarith
  have hρt0 : 0 ≤ ρt := by
    have h1 : (0 : ℝ) ≤ ρw / (1 + WL * (1 - ρw)) := div_nonneg hρw0 hm2.le
    have h2 : (0 : ℝ) ≤ (1 + ρw) * (174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59) :=
      mul_nonneg (by linarith) hC0
    by_contra hc
    push Not at hc
    have := mul_neg_of_neg_of_pos hc hdenH
    linarith
  have hTot : 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 + value w.toBits / 2 ^ 59 +
      ρw * W / (1 + W * (1 - ρw)) ≤ ρt * (2 * Real.artanh va) := by
    have h1 : W * ((1 + ρw) * (174 / 100 / 2 ^ 53 * (WH * (1 + ρw)) + 1 / 2 ^ 59)) +
        W * (ρw / (1 + WL * (1 - ρw))) ≤ W * (ρt * (1 - aH)) := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left hρt hW0.le
    have h2 : W * (ρt * (1 - aH)) ≤ ρt * (2 * va) := by
      have := mul_le_mul_of_nonneg_left hWa hρt0
      linarith
    have h3 : ρt * (2 * va) ≤ ρt * (2 * Real.artanh va) := mul_le_mul_of_nonneg_left hart hρt0
    linarith
  have hN3 : Near (Log1p.log1p w).toBits (2 * Real.artanh va) (ρt * (2 * Real.artanh va)) := by
    rw [← hLW]
    rw [← hLW] at hTot
    exact hN2.mono hTot
  have hYu : 2 * Real.artanh va ≤ 1 := by
    rw [← hLW]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + W)
    have h2 : W ≤ 2 * (1 / 8) / (1 - 1 / 8) := by
      rw [hW]
      exact div_le_div₀ (by norm_num) (by linarith) (by norm_num) (by linarith)
    linarith [(by norm_num : (2 : ℝ) * (1 / 8) / (1 - 1 / 8) ≤ 1)]
  have hρt2 : ρt ≤ 1 / 2 ^ 52 := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have hY0 : 2 * (1 / 2 ^ 28) ≤ 2 * Real.artanh va := by linarith [h28.trans haL]
  have hTs : ρt * (2 * Real.artanh va) ≤ 1 / 2 ^ 52 := by
    have := mul_le_mul hρt2 hYu (by linarith) (by positivity)
    linarith
  have hN4 := hN3.half
    (by
      rw [abs_of_nonneg (by linarith)]
      linarith [(by norm_num : (1 : ℝ) / 2 ^ 998 + 1 / 2 ^ 52 ≤ 2 * (1 / 2 ^ 28))])
    (by
      rw [abs_of_nonneg (by linarith)]
      linarith [(by norm_num : (1 : ℝ) + 1 / 2 ^ 52 < 2 ^ 1000)])
  rw [show 2 * Real.artanh va / 2 = Real.artanh va by ring] at hN4
  rw [F64Bits.toBits_mul, show (0.5 : Float).toBits = 0x3FE0000000000000 from rfl]
  have hY1 : 0 ≤ Real.artanh va := by linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 28)]
  refine hN4.within_two_rel (ρ := ρt) (by rw [abs_of_nonneg hY1]; linarith) hρt0 hρt1 ?_ ?_
  · rw [abs_of_nonneg hY1]
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 1020 ≤ 1 / 2 ^ 28)]
  · rw [abs_of_nonneg hY1]
    linarith [(by norm_num : (1 : ℝ) < 2 ^ 1022)]

#print axioms atanh_q
#print axioms atanh_piece
#print axioms atanh_piece_rel

end Library.Numerics.Float64.Asinh.AtanhTheoremSmall
