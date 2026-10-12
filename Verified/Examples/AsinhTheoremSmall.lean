import Verified.Examples.AsinhTheoremCompose
import Verified.Examples.AsinhTheoremMid

/-!
`Asinh.asinh` from `2 ^ -28` to 2, before the sign: the code returns `log1p u` with
`u = |x| + x²/(1 + √(1 + x²))`, whose exact value `U` satisfies `1 + U = |x| + √(1 + x²)`, so
`log (1 + U) = arsinh |x|`.  `asinh_e` follows the relative errors of `x²`, `1 + x²`, its root,
`1 + √(1 + x²)`, and the quotient `e` with constants for `|x| ≤ aH`.  `asinh_piece` adds the last
rounding as half a spacing and compares the bound of `Log1pTheoremNear.log1p_near` plus the
argument term with two spacings of a binade; `asinh_piece_rel` bounds the total relative to
`arsinh |x|` for small inputs.
-/

namespace Verified.Examples.AsinhTheoremSmall
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RelError F64Near F64HalfUlp Log1pTheoremNear
  AsinhTheoremCompose AsinhTheoremMid

set_option exponentiation.threshold 4096

/-- `e = x²/(1 + √(1 + x²))` relative to its exact value, for `2 ^ -28 ≤ |x| ≤ aH`. -/
theorem asinh_e (x : Float) (hx : Finite x.toBits) (aH tq rq rr td rd re sH : ℝ)
    (h28 : 1 / 2 ^ 28 ≤ |value x.toBits|) (haH : |value x.toBits| ≤ aH) (haH3 : aH ≤ 3)
    (htq0 : tq ≤ 1001 / 1000 / 2 ^ 53) (htq : (1001 / 1000 / 2 ^ 53 - tq) * aH ^ 2 ≤ tq)
    (hrq : tq + (1 + tq) / 2 ^ 53 ≤ rq) (hrq1 : rq < 1) (hrr : rq + (1 + rq) / 2 ^ 53 ≤ rr)
    (hsH0 : 0 ≤ sH) (hsH : 1 + aH ^ 2 ≤ sH ^ 2)
    (htd0 : td ≤ rr) (htd : (rr - td) * sH ≤ td) (hrd : td + (1 + td) / 2 ^ 53 ≤ rd)
    (hrd1 : rd ≤ 1 / 2)
    (hre : (1001 / 1000 / 2 ^ 53 + rd) / (1 - rd) + (1 + 1001 / 1000 / 2 ^ 53) / (1 - rd) / 2 ^ 53 +
      1 / 1000 / 2 ^ 53 ≤ re) :
    RApprox (x * x / (1.0 + (1.0 + x * x).sqrt)).toBits
      (|value x.toBits| * |value x.toBits| /
        (1 + Real.sqrt (1 + |value x.toBits| * |value x.toBits|))) re := by
  set a := |value x.toBits| with ha
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) h28
  have haH0 : 0 ≤ aH := ha0.le.trans haH
  have hsq : 1 / 2 ^ 56 ≤ a * a := by
    have := mul_le_mul h28 h28 (by positivity) ha0.le
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 28 * (1 / 2 ^ 28) = 1 / 2 ^ 56)]
  have haa : a * a ≤ aH ^ 2 := by
    rw [sq]
    exact mul_le_mul haH haH ha0.le haH0
  have haH9 : aH ^ 2 ≤ 9 := by
    rw [sq]
    have := mul_le_mul haH3 haH3 haH0 (by norm_num)
    linarith
  -- `x * x`
  have hp : RApprox (x * x).toBits (a * a) (1001 / 1000 / 2 ^ 53) := by
    have hmul := approx_mul (approx_self x.toBits hx) (approx_self x.toBits hx) a a
      le_rfl le_rfl (a * a) (le_of_eq (by ring))
      (by linarith [(by norm_num : (9 : ℝ) < 2 ^ 1022)])
    rw [← F64Bits.toBits_mul] at hmul
    refine ⟨mul_pos ha0 ha0, ?_⟩
    have hv : value x.toBits * value x.toBits = a * a := by
      rw [ha, ← abs_mul, abs_mul_self]
    rw [hv] at hmul
    refine hmul.mono ?_
    have h4 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 1000 / 2 ^ 53 * (a * a) := by
      have h5 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 1000 / 2 ^ 53 * (1 / 2 ^ 56) := by norm_num
      have h6 := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 1 / 1000 / 2 ^ 53)
      linarith
    linarith
  have htq0' : 0 ≤ tq := by
    have h1 : (0 : ℝ) ≤ (1001 / 1000 / 2 ^ 53 - tq) * aH ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg _)
    linarith
  -- `1 + x * x`
  have hq := (rapprox_add one_rapprox hp tq (by
    have h1 : (1001 / 1000 / 2 ^ 53 - tq) * (a * a) ≤ (1001 / 1000 / 2 ^ 53 - tq) * aH ^ 2 :=
      mul_le_mul_of_nonneg_left haa (by linarith)
    linarith) (by
      have h1 : 1 + tq ≤ 2 := by linarith [(by norm_num : (1001 : ℝ) / 1000 / 2 ^ 53 ≤ 1)]
      have h2 : 1 + a * a ≤ 10 := by linarith
      have h3 := mul_le_mul h1 h2 (by positivity) (by norm_num)
      linarith [(by norm_num : (2 : ℝ) * 10 < 2 ^ 1023)])).mono hrq
  rw [← F64Bits.toBits_add] at hq
  -- the square root
  have hr := (rapprox_sqrt hq hrq1).mono hrr
  rw [← F64Bits.toBits_sqrt] at hr
  set s := Real.sqrt (1 + a * a) with hs
  have hs1 : 1 ≤ s := by
    rw [hs, Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  have hsHs : s ≤ sH := by
    rw [hs, Real.sqrt_le_left hsH0]
    linarith
  have hs4 : s ≤ 4 := by
    rw [hs, Real.sqrt_le_left (by norm_num)]
    linarith
  have htd0' : 0 ≤ td := by
    have := mul_nonneg (sub_nonneg.mpr htd0) hsH0
    linarith
  have htd1 : td ≤ 1 := by
    have : (0 : ℝ) ≤ (1 + td) / 2 ^ 53 := by positivity
    linarith
  -- `1 + √(1 + x * x)`
  have hd := (rapprox_add one_rapprox hr td (by
    have h1 : (rr - td) * s ≤ (rr - td) * sH := mul_le_mul_of_nonneg_left hsHs (by linarith)
    linarith) (by
      have h3 := mul_le_mul (by linarith : 1 + td ≤ 2) (by linarith : 1 + s ≤ 5) (by linarith)
        (by norm_num)
      linarith [(by norm_num : (2 : ℝ) * 5 < 2 ^ 1023)])).mono hrd
  rw [← F64Bits.toBits_add] at hd
  -- the quotient
  have hpos : 0 < 1 + s := by linarith
  have h1s : a * a / 5 ≤ a * a / (1 + s) :=
    div_le_div_of_nonneg_left (by positivity) hpos (by linarith)
  have hs1' : a * a / (1 + s) ≤ a * a := div_le_self (by positivity) (by linarith)
  have he := rapprox_div hp hd (by linarith) (1 / 1000 / 2 ^ 53)
    (by
      have h2 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 1000 / 2 ^ 53 * (1 / 2 ^ 56 / 5) := by norm_num
      have h3 : 1 / 2 ^ 56 / 5 ≤ a * a / 5 := by linarith
      have h4 := mul_le_mul_of_nonneg_left (h3.trans h1s)
        (by norm_num : (0 : ℝ) ≤ 1 / 1000 / 2 ^ 53)
      linarith)
    (by
      have h2 : (1 + 1001 / 1000 / 2 ^ 53) / (1 - rd) ≤ 4 := by
        rw [div_le_iff₀ (by linarith)]
        linarith [(by norm_num : (1001 : ℝ) / 1000 / 2 ^ 53 ≤ 1)]
      have h3 : 0 ≤ a * a / (1 + s) := by positivity
      have h4 := mul_le_mul h2 hs1' h3 (by norm_num)
      linarith [(by norm_num : (4 : ℝ) * 9 < 2 ^ 1022)])
  rw [← F64Bits.toBits_div] at he
  exact he.mono hre

theorem e_eq (a : ℝ) (ha : 0 ≤ a) :
    a * a / (1 + Real.sqrt (1 + a * a)) = Real.sqrt (1 + a * a) - 1 := by
  obtain ⟨t, ht⟩ : ∃ t, t = Real.sqrt (1 + a * a) := ⟨_, rfl⟩
  rw [← ht]
  have htt : t * t = 1 + a * a := by rw [ht]; exact Real.mul_self_sqrt (by positivity)
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  rw [div_eq_iff (by linarith)]
  linear_combination -htt

theorem arsinh_eq (a : ℝ) : Real.arsinh a = Real.log (a + Real.sqrt (1 + a * a)) := by
  rw [Real.arsinh, sq]

/-- A range `[aL, aH]` of `|x|` with a constant bound `E` of `log1p` and `K` of the argument
term, against two spacings of binade `n`; `sL` and `sH` bound `√(1 + a²)` at the ends. -/
theorem asinh_piece (x : Float) (hx : Finite x.toBits) (aL aH re sL sH h E K YL : ℝ) (g n : ℕ)
    (he : RApprox (x * x / (1.0 + (1.0 + x * x).sqrt)).toBits
      (|value x.toBits| * |value x.toBits| /
        (1 + Real.sqrt (1 + |value x.toBits| * |value x.toBits|))) re)
    (haL : aL ≤ |value x.toBits|) (haH : |value x.toBits| ≤ aH) (h28 : 1 / 2 ^ 28 ≤ aL)
    (hsL0 : 0 ≤ sL) (hsL : sL ^ 2 ≤ 1 + aL ^ 2) (hsH0 : 0 ≤ sH) (hsH : 1 + aH ^ 2 ≤ sH ^ 2)
    (hg : g ≤ 1023) (hh : 2 ^ g / 2 / 2 ^ 1074 ≤ h)
    (hgW : aH + (sH - 1) + re * (sH - 1) < 2 ^ (53 + g) / 2 ^ 1074)
    (hE : ∀ v : ℝ, aL + (sL - 1) - (re * (sH - 1) + h) ≤ v →
      v ≤ aH + (sH - 1) + (re * (sH - 1) + h) → errBound v ≤ E)
    (hm : re * (sH - 1) + h < aL + sL)
    (hK : re * (sH - 1) + h ≤ K * (aL + sL - (re * (sH - 1) + h)))
    (hδ : re * (sH - 1) + h ≤ 1 / 2 ^ 40)
    (hYL : YL ≤ Real.log (aL + sL)) (hEK : E + K ≤ 1) (haH3 : aH ≤ 3)
    (hn1 : 1 ≤ n) (hn : n < 2047)
    (hB : value (UInt64.ofNat (n * 2 ^ 52)) + (E + K) ≤ YL)
    (hT : E + K < 2 * ((2 : ℝ) ^ (n - 1) / 2 ^ 1074)) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits := by
  set a := |value x.toBits| with ha
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) (h28.trans haL)
  obtain ⟨haf, hav⟩ := AtanTheoremReduce.abs_facts x hx
  have hA : FApprox x.abs a 0 := by
    refine ⟨haf, ?_⟩
    rw [hav, sub_self, abs_zero]
  have hre0 : 0 ≤ re := he.rho_nonneg
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (1 + a * a) := ⟨_, rfl⟩
  have hss : s * s = 1 + a * a := by rw [hsdef]; exact Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hsHs : s ≤ sH := by
    rw [hsdef, Real.sqrt_le_left hsH0]
    have := mul_le_mul haH haH ha0.le (ha0.le.trans haH)
    nlinarith
  have hsLs : sL ≤ s := by
    rw [hsdef, Real.le_sqrt hsL0 (by positivity)]
    have := mul_le_mul haL haL (le_trans (by positivity) h28) ha0.le
    nlinarith
  have hee : a * a / (1 + Real.sqrt (1 + a * a)) = s - 1 := by rw [hsdef]; exact e_eq a ha0.le
  rw [hee] at he
  have hs1 : 1 ≤ s := by nlinarith
  have heH : re * (s - 1) ≤ re * (sH - 1) := mul_le_mul_of_nonneg_left (by linarith) hre0
  -- the last addition
  have hw0 := fapprox_add_half hA he.2 g hg (by
    rw [abs_of_nonneg (by linarith), zero_add]
    linarith)
  obtain ⟨w, hwdef⟩ : ∃ w : Float, w = x.abs + x * x / (1.0 + (1.0 + x * x).sqrt) := ⟨_, rfl⟩
  rw [← hwdef] at hw0
  rw [← hwdef]
  have hd : |value w.toBits - (a + (s - 1))| ≤ re * (sH - 1) + h := by
    have := hw0.2
    linarith
  have hda := abs_le.mp hd
  have hw29 : 1 / 2 ^ 29 ≤ value w.toBits := by
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 29 + 1 / 2 ^ 40 ≤ 1 / 2 ^ 28)]
  have hN := (log1p_near w hw0.1 hw29).mono (hE _ (by linarith) (by linarith))
  have hm' : 0 < aL + sL - (re * (sH - 1) + h) := by linarith
  have hN2 := near_compose hN hd hm' (by linarith) (by linarith)
  have hK' : (re * (sH - 1) + h) / (aL + sL - (re * (sH - 1) + h)) ≤ K := by
    rw [div_le_iff₀ hm']
    exact hK
  have hY : Real.log (1 + (a + (s - 1))) = Real.arsinh a := by
    rw [arsinh_eq, ← hsdef]
    congr 1
    ring
  rw [hY] at hN2
  have hN3 := hN2.mono (E' := E + K) (by linarith only [hK'])
  have hYL' : YL ≤ Real.arsinh a := by
    rw [arsinh_eq, ← hsdef]
    exact hYL.trans (Real.log_le_log (by linarith only [hsL0, h28]) (by linarith only [haL, hsLs]))
  have hs4 : s ≤ 4 := by
    by_contra hc
    push Not at hc
    have h1 := mul_lt_mul' hc.le hc (by norm_num) (by linarith only [hc])
    have h2 := mul_le_mul haH haH ha0.le (ha0.le.trans haH)
    have h3 := mul_le_mul haH3 haH3 (ha0.le.trans haH) (by norm_num)
    linarith only [h1, h2, hss, h3]
  have hYu : Real.arsinh a ≤ 6 := by
    rw [← hY]
    have := Real.log_le_sub_one_of_pos (by linarith only [ha0, hs1] : (0 : ℝ) < 1 + (a + (s - 1)))
    linarith only [this, hs4, haH, haH3]
  refine hN3.within_two n hn1 hn ?_ hT ?_
  · rw [abs_of_nonneg (Real.arsinh_nonneg_iff.mpr ha0.le)]
    generalize value (UInt64.ofNat (n * 2 ^ 52)) = B at hB ⊢
    linarith only [hB, hYL']
  · rw [abs_of_nonneg (Real.arsinh_nonneg_iff.mpr ha0.le)]
    linarith only [hYu, (by norm_num : (6 : ℝ) < 2 ^ 1023)]

/-- A range `[aL, aH]` of small `|x|` with a bound relative to `arsinh |x|`. -/
theorem asinh_piece_rel (x : Float) (hx : Finite x.toBits) (aL aH re sH UL UH θu ρu ρt : ℝ)
    (he : RApprox (x * x / (1.0 + (1.0 + x * x).sqrt)).toBits
      (|value x.toBits| * |value x.toBits| /
        (1 + Real.sqrt (1 + |value x.toBits| * |value x.toBits|))) re)
    (haL : aL ≤ |value x.toBits|) (haH : |value x.toBits| ≤ aH) (h28 : 1 / 2 ^ 28 ≤ aL)
    (hsH0 : 0 ≤ sH) (hsH : 1 + aH ^ 2 ≤ sH ^ 2)
    (hUL0 : 0 ≤ UL) (hUL : UL ≤ aL) (hUH : aH + (sH - 1) ≤ UH)
    (hθ0 : θu ≤ re) (hθ : (re - θu) * aH / 2 ≤ θu)
    (hρu : θu + (1 + θu) / 2 ^ 53 ≤ ρu) (hρu1 : ρu ≤ 1 / 2 ^ 50)
    (hUH1 : UH * (1 + ρu) ≤ 285 / 1000)
    (hρt : ((1 + ρu) * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59) +
      ρu / (1 + UL * (1 - ρu))) * (2 + UH) ≤ 2 * ρt)
    (hρt1 : ρt * (2 ^ 52 + 1) < 1) :
    F64SignedRounding.WithinSteps 2 (Real.arsinh |value x.toBits|)
      (Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))).toBits := by
  set a := |value x.toBits| with ha
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) (h28.trans haL)
  obtain ⟨haf, hav⟩ := AtanTheoremReduce.abs_facts x hx
  have hA : RApprox x.abs.toBits a 0 := by
    have h := rapprox_self x.abs.toBits haf (by rw [hav]; exact ha0)
    rwa [hav] at h
  have hre0 : 0 ≤ re := he.rho_nonneg
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt (1 + a * a) := ⟨_, rfl⟩
  have hss : s * s = 1 + a * a := by rw [hsdef]; exact Real.mul_self_sqrt (by positivity)
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have hsHs : s ≤ sH := by
    rw [hsdef, Real.sqrt_le_left hsH0]
    have := mul_le_mul haH haH ha0.le (ha0.le.trans haH)
    nlinarith
  have hee : a * a / (1 + Real.sqrt (1 + a * a)) = s - 1 := by rw [hsdef]; exact e_eq a ha0.le
  have hes : s - 1 ≤ a * a / 2 := by
    rw [← hee]
    apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
    have : 1 ≤ Real.sqrt (1 + a * a) := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      nlinarith
    linarith
  rw [hee] at he
  have hs1 : 1 ≤ s := by nlinarith
  have hθ0' : 0 ≤ θu := by
    have := mul_nonneg (mul_nonneg (sub_nonneg.mpr hθ0) (ha0.le.trans haH)) (by norm_num : (0:ℝ) ≤ 1 / 2)
    linarith
  -- the last addition, relative
  have hu := (rapprox_add hA he θu (by
    have h1 : (re - θu) * (s - 1) ≤ (re - θu) * (a * a / 2) :=
      mul_le_mul_of_nonneg_left hes (sub_nonneg.mpr hθ0)
    have h2 : (re - θu) * aH / 2 * a ≤ θu * a := mul_le_mul_of_nonneg_right hθ ha0.le
    have h3 : (re - θu) * (a * a / 2) ≤ (re - θu) * aH / 2 * a := by
      have := mul_le_mul_of_nonneg_left haH (mul_nonneg (sub_nonneg.mpr hθ0) ha0.le)
      linarith
    linarith) (by
      have h1 : a + (s - 1) ≤ UH := by linarith
      have h2 : 1 + θu ≤ 2 := by
        have : (0 : ℝ) ≤ (1 + θu) / 2 ^ 53 := by positivity
        linarith [(by norm_num : (1 : ℝ) / 2 ^ 50 ≤ 1)]
      have h3 := mul_le_mul h2 h1 (by linarith) (by norm_num)
      linarith [(by norm_num : (2 : ℝ) * (285 / 1000) < 2 ^ 1023),
        mul_nonneg (by linarith : (0 : ℝ) ≤ UH) (by linarith : (0 : ℝ) ≤ ρu)])).mono hρu
  rw [← F64Bits.toBits_add] at hu
  obtain ⟨w, hwdef⟩ : ∃ w : Float, w = x.abs + x * x / (1.0 + (1.0 + x * x).sqrt) := ⟨_, rfl⟩
  rw [← hwdef] at hu
  rw [← hwdef]
  set U := a + (s - 1) with hU
  have hU0 : 0 < U := by linarith
  have hUUH : U ≤ UH := by linarith
  have hUL' : UL ≤ U := by linarith
  have hd : |value w.toBits - U| ≤ ρu * U := hu.2.2
  have hda := abs_le.mp hd
  have hρu0 : 0 ≤ ρu := le_trans (by positivity) hρu
  have hρuU : ρu * U ≤ U / 2 := by
    have := mul_le_mul_of_nonneg_right (hρu1.trans (by norm_num) : ρu ≤ 1 / 2) hU0.le
    linarith
  have hw29 : 1 / 2 ^ 29 ≤ value w.toBits := by
    have : 1 / 2 ^ 28 ≤ U := by linarith
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 29 ≤ 1 / 2 ^ 28 / 2)]
  have hwu : value w.toBits ≤ U * (1 + ρu) := by linarith [hda.2]
  have hw285 : value w.toBits ≤ 285 / 1000 := by
    have := mul_le_mul_of_nonneg_right hUUH (by linarith : (0 : ℝ) ≤ 1 + ρu)
    linarith
  have hN := log1p_near w hu.2.1 hw29
  rw [errBound, if_pos hw285] at hN
  have hm1 : 0 ≤ U * (1 - ρu) := mul_nonneg hU0.le (by linarith)
  have hm : 0 < 1 + U * (1 - ρu) := by linarith
  have hN2 := near_compose hN hd hm (by linarith [hda.1]) (by linarith [mul_nonneg hρu0 hU0.le])
  have hvw0 : 0 ≤ value w.toBits := by linarith [(by positivity : (0 : ℝ) < 1 / 2 ^ 29)]
  have hUH0 : 0 ≤ UH := hU0.le.trans hUUH
  have hC0 : 0 ≤ 174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59 :=
    add_nonneg (mul_nonneg (by norm_num) (mul_nonneg hUH0 (by linarith))) (by norm_num)
  have hE1 : 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 + value w.toBits / 2 ^ 59 ≤
      U * ((1 + ρu) * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59)) := by
    have h1 : value w.toBits ≤ UH * (1 + ρu) := by
      have := mul_le_mul_of_nonneg_right hUUH (by linarith : (0 : ℝ) ≤ 1 + ρu)
      linarith
    have h2 : 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 ≤
        174 / 100 / 2 ^ 53 * (value w.toBits * (UH * (1 + ρu))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [sq]
      exact mul_le_mul_of_nonneg_left h1 hvw0
    have h3 : value w.toBits * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59) ≤
        U * (1 + ρu) * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59) :=
      mul_le_mul_of_nonneg_right hwu hC0
    calc 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 + value w.toBits / 2 ^ 59
        ≤ 174 / 100 / 2 ^ 53 * (value w.toBits * (UH * (1 + ρu))) + value w.toBits / 2 ^ 59 := by
          linarith
      _ = value w.toBits * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59) := by ring
      _ ≤ U * (1 + ρu) * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59) := h3
      _ = _ := by ring
  have hm2 : 0 < 1 + UL * (1 - ρu) := by
    have := mul_nonneg hUL0 (by linarith : (0 : ℝ) ≤ 1 - ρu)
    linarith
  have hE2 : ρu * U / (1 + U * (1 - ρu)) ≤ U * (ρu / (1 + UL * (1 - ρu))) := by
    rw [mul_div_assoc', div_le_div_iff₀ hm hm2]
    have : UL * (1 - ρu) ≤ U * (1 - ρu) := mul_le_mul_of_nonneg_right hUL' (by linarith)
    have h4 := mul_le_mul_of_nonneg_left this (mul_nonneg hρu0 hU0.le)
    calc ρu * U * (1 + UL * (1 - ρu)) = ρu * U + ρu * U * (UL * (1 - ρu)) := by ring
      _ ≤ ρu * U + ρu * U * (U * (1 - ρu)) := by linarith
      _ = U * ρu * (1 + U * (1 - ρu)) := by ring
  have hY : Real.log (1 + U) = Real.arsinh a := by
    rw [arsinh_eq, ← hsdef, hU]
    congr 1
    ring
  have hpade : 2 * U / (2 + UH) ≤ Real.arsinh a := by
    rw [← hY]
    have h1 := log_pade U hU0
    have h2 : 2 * U / (2 + UH) ≤ 2 * U / (2 + U) :=
      div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith)
    linarith
  have hK0 : 0 ≤ (1 + ρu) * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59) +
      ρu / (1 + UL * (1 - ρu)) :=
    add_nonneg (mul_nonneg (by linarith) hC0) (div_nonneg hρu0 hm2.le)
  have hTot : 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 + value w.toBits / 2 ^ 59 +
      ρu * U / (1 + U * (1 - ρu)) ≤ ρt * Real.arsinh a := by
    set K1 := (1 + ρu) * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59) +
      ρu / (1 + UL * (1 - ρu)) with hK1
    have h1 : 174 / 100 / 2 ^ 53 * value w.toBits ^ 2 + value w.toBits / 2 ^ 59 +
        ρu * U / (1 + U * (1 - ρu)) ≤ U * K1 := by
      have e : U * K1 = U * ((1 + ρu) * (174 / 100 / 2 ^ 53 * (UH * (1 + ρu)) + 1 / 2 ^ 59)) +
          U * (ρu / (1 + UL * (1 - ρu))) := by rw [hK1]; ring
      linarith [hE1, hE2, e]
    have h2 : U * K1 = K1 * (2 + UH) / 2 * (2 * U / (2 + UH)) := by
      field_simp
    have h3 : K1 * (2 + UH) / 2 ≤ ρt := by linarith
    have h4 : 0 ≤ 2 * U / (2 + UH) := by positivity
    have h5 : K1 * (2 + UH) / 2 * (2 * U / (2 + UH)) ≤ ρt * (2 * U / (2 + UH)) :=
      mul_le_mul_of_nonneg_right h3 h4
    have hρt0 : 0 ≤ ρt := by
      have : 0 ≤ K1 * (2 + UH) := mul_nonneg hK0 (by linarith)
      linarith
    have h6 := mul_le_mul_of_nonneg_left hpade hρt0
    linarith
  rw [hY] at hN2
  have hN3 := hN2.mono hTot
  have hY0 : 0 ≤ Real.arsinh a := Real.arsinh_nonneg_iff.mpr ha0.le
  have hρt0 : 0 ≤ ρt := by
    have := mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ 2 + UH)
    linarith
  refine hN3.within_two_rel (by rw [abs_of_nonneg hY0]) hρt0 hρt1 ?_ ?_
  · rw [abs_of_nonneg hY0]
    have hUH2 : UH ≤ 2 := by linarith [mul_nonneg hUH0 hρu0]
    have h3 : U / 2 ≤ 2 * U / (2 + UH) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      have := mul_le_mul_of_nonneg_left hUH2 hU0.le
      linarith
    have h2 : 1 / 2 ^ 28 ≤ U := by linarith only [h28, haL, hs1]
    linarith only [h3, h2, hpade, (by norm_num : (1 : ℝ) / 2 ^ 1020 ≤ 1 / 2 ^ 28 / 2)]
  · rw [abs_of_nonneg hY0, ← hY]
    have := Real.log_le_sub_one_of_pos (by linarith only [hU0] : (0 : ℝ) < 1 + U)
    linarith only [this, hUUH, hUH1, mul_nonneg hUH0 hρu0, (by norm_num : (1 : ℝ) < 2 ^ 1022)]

#print axioms asinh_e
#print axioms asinh_piece
#print axioms asinh_piece_rel

end Verified.Examples.AsinhTheoremSmall
