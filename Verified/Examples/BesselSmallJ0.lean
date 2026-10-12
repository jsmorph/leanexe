import Verified.Examples.BesselSmallEval
import Verified.Examples.BesselJ0Large

/-!
`Bessel.j0 x` for `|x| < 2`: the result is finite and lies within `(41/10) u` of `J₀(x)`, with
`u = 2 ^ -53` (`j0_small`).  The code has four paths by the high word of `|x|`: 1 below `2^-27`,
`1 - x²/4` below `2^-13`, `1 + z (r/s - 1/4)` below 1, and `(1 + x/2)(1 - x/2) + z (r/s)` from 1,
with `z = x x`, `r = z R(z)`, and `s = S(z)`.  `form1` and `form2` follow the last two through
`F64Approx`, with the Horner bounds of `BesselSmallEval.horner_at` checked by the kernel on one
interval each (`horner_facts`), the exact `x/2` of `half_exact`, and the exact `1 - x/2` of
Sterbenz's lemma; `BesselSmallApprox.j0_approx` adds the error of fdlibm's approximation.  The
first two paths need only `J₀ = 1 - x²/4 + O(x⁴)` from the series.
-/

namespace Verified.Examples.BesselSmallJ0
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The words of `R` and `S` of `j0` below 2. -/
def r0w : List UInt64 :=
  [0x3F8FFFFFFFFFFFFD, 0xBF28E6A5B61AC6E9, 0x3EBEB1D10C503919, 0xBE33D5E773D63FCE]
def s0w : List UInt64 :=
  [0x3F8FFCE882C8C2A4, 0x3F1EA6D2DD57DBF4, 0x3EA13B54CE84D5A9, 0x3E1408BCF4745D8F]

theorem words : (∀ w ∈ r0w, Finite w) ∧ (∀ w ∈ s0w, Finite w) := by
  unfold CodeLib.IEEE64.Finite
  decide

theorem lists : r0w.map ratOfWord = R0 ∧ 1 :: s0w.map ratOfWord = S0 := ⟨rfl, rfl⟩

def lo1 : ℚ := -1 / 2 ^ 50
def hi1 : ℚ := 1 + 1 / 2 ^ 50
def lo2 : ℚ := 1 - 1 / 2 ^ 50
def hi2 : ℚ := 4 + 1 / 2 ^ 48

theorem horner_facts :
    hornerOK R0 lo1 hi1 = true ∧ hornerOK S0 lo1 hi1 = true ∧
      hornerOK R0 lo2 hi2 = true ∧ hornerOK S0 lo2 hi2 = true ∧
      hornerErr R0 lo1 hi1 ≤ 17 / 1000 / 2 ^ 53 ∧ magBound (derivP R0) lo1 hi1 ≤ 1 / 5000 ∧
      magBound R0 lo1 hi1 ≤ 16 / 1000 ∧
      hornerErr S0 lo1 hi1 ≤ 1048 / 1000 / 2 ^ 53 ∧ magBound (derivP S0) lo1 hi1 ≤ 16 / 1000 ∧
      9999 / 10000 ≤ lowBound S0 lo1 hi1 ∧
      hornerErr R0 lo2 hi2 ≤ 18 / 1000 / 2 ^ 53 ∧ magBound (derivP R0) lo2 hi2 ≤ 1 / 5000 ∧
      magBound R0 lo2 hi2 ≤ 155 / 10000 ∧
      hornerErr S0 lo2 hi2 ≤ 1198 / 1000 / 2 ^ 53 ∧ magBound (derivP S0) lo2 hi2 ≤ 17 / 1000 ∧
      1015 / 1000 ≤ lowBound S0 lo2 hi2 := by
  decide +kernel

/-- `R(ẑ)` and `S(ẑ)` against `R(z)` and `S(z)`, with `|ẑ - z| ≤ δ` and both in `[lo, hi]`. -/
theorem rs_at (zf : Float) (hzf : Finite zf.toBits) (z δ : ℝ) (lo hi : ℚ)
    (hR : hornerOK R0 lo hi = true) (hS : hornerOK S0 lo hi = true)
    (h1 : (lo : ℝ) ≤ value zf.toBits) (h2 : value zf.toBits ≤ hi) (h3 : (lo : ℝ) ≤ z)
    (h4 : z ≤ hi) (hδ : |value zf.toBits - z| ≤ δ) :
    FApprox (hornerF (r0w.map Float.ofBits) zf) (eval R0 z)
        (hornerErr R0 lo hi + magBound (derivP R0) lo hi * δ) ∧
      FApprox (hornerF (1.0 :: s0w.map Float.ofBits) zf) (eval S0 z)
        (hornerErr S0 lo hi + magBound (derivP S0) lo hi * δ) := by
  obtain ⟨wr, ws⟩ := words
  obtain ⟨b1, b2⟩ := words_rel r0w wr
  obtain ⟨c1, c2⟩ := words_rel_one s0w ws
  exact ⟨horner_at _ _ R0 b1 b2 (by decide) lo hi hR zf hzf z δ h1 h2 h3 h4 hδ,
    horner_at _ _ S0 c1 c2 (by decide) lo hi hS zf hzf z δ h1 h2 h3 h4 hδ⟩

theorem quarter_bits : (0.25 : Float).toBits = 0x3FD0000000000000 := rfl

theorem fapprox_quarter : FApprox 0.25 (1 / 4) 0 := by
  unfold FApprox Approx
  rw [quarter_bits, ← ratOfWord_cast]
  have : ratOfWord 0x3FD0000000000000 = 1 / 4 := by decide +kernel
  rw [this]
  exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩

/-- `1 + z (r/s - 1/4)` for `0 ≤ x ≤ 1`. -/
theorem form1 (xa : Float) (hf : Finite xa.toBits) (v : ℝ) (hv : value xa.toBits = v)
    (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    FApprox (1.0 + xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
        hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa) - 0.25))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) (2 * 𝐮) := by
  subst hv
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  obtain ⟨k1, k2, -, -, e1, e2, e3, e4, e5, e6, -⟩ := horner_facts
  set v := value xa.toBits
  have hv2 : v ^ 2 ≤ 1 := by nlinarith
  have hz := sq_near xa hf 1 (by rw [abs_of_nonneg h0]; exact h1) (by norm_num)
  simp only [mul_one] at hz
  set z := v ^ 2
  have hz0 : 0 ≤ z := by positivity
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (xa * xa) hz.1 z _ lo1 hi1 k1 k2
    (by simp only [lo1]; push_cast; norm_num at hzv ⊢; linarith)
    (by simp only [hi1]; push_cast; norm_num at hzv ⊢; linarith)
    (by simp only [lo1]; push_cast; linarith) (by simp only [hi1]; push_cast; linarith) hz.2
  have hR' : FApprox (hornerF (r0w.map Float.ofBits) (xa * xa)) (eval R0 z) (2 / 100 * 𝐮) := by
    refine fmono hR ?_
    have a1 := (Rat.cast_le (K := ℝ)).mpr e1
    have a2 := (Rat.cast_le (K := ℝ)).mpr e2
    push_cast at a1 a2
    have : (0 : ℝ) ≤ magBound (derivP R0) lo1 hi1 := (abs_nonneg _).trans
      (magBound_sound _ lo1 hi1 0 (by norm_num [lo1]) (by norm_num [hi1]))
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (eval S0 z)
      (107 / 100 * 𝐮) := by
    refine fmono hS ?_
    have a1 := (Rat.cast_le (K := ℝ)).mpr e4
    have a2 := (Rat.cast_le (K := ℝ)).mpr e5
    push_cast at a1 a2
    have : (0 : ℝ) ≤ magBound (derivP S0) lo1 hi1 := (abs_nonneg _).trans
      (magBound_sound _ lo1 hi1 0 (by norm_num [lo1]) (by norm_num [hi1]))
    rw [hu]
    nlinarith
  have hRm : |eval R0 z| ≤ 16 / 1000 := by
    have := magBound_sound R0 lo1 hi1 z (by simp only [lo1]; push_cast; linarith)
      (by simp only [hi1]; push_cast; linarith)
    have a := (Rat.cast_le (K := ℝ)).mpr e3
    push_cast at a
    linarith
  have hSm : 9999 / 10000 ≤ eval S0 z := by
    have := lowBound_sound S0 lo1 hi1 z (by simp only [lo1]; push_cast; linarith)
      (by simp only [hi1]; push_cast; linarith)
    have a := (Rat.cast_le (K := ℝ)).mpr e6
    push_cast at a
    linarith
  have hzR : |z * eval R0 z| ≤ 16 / 1000 := by
    rw [abs_mul, abs_of_nonneg hz0]; nlinarith [abs_nonneg (eval R0 z)]
  have hr := fapprox_mul hz hR' 1 (16 / 1000) (by rw [abs_of_nonneg hz0]; exact hv2) hRm _ le_rfl
    (by rw [hu]; norm_num)
  have hr' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa)) (z * eval R0 z)
      (6 / 100 * 𝐮) := fmono hr (by rw [hu]; norm_num)
  have hq := fapprox_div hr' hS' (16 / 1000) (9999 / 10000) hzR
    (by rw [abs_of_pos (by linarith)]; exact hSm) (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (z * eval R0 z / eval S0 z)
      (11 / 100 * 𝐮) := fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R0 z / eval S0 z| ≤ 17 / 1000 := by
    rw [abs_div, abs_of_pos (show 0 < eval S0 z by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  have ht := fapprox_sub_half hq' fapprox_quarter 1020 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1020) / 2 ^ 1074 = 1 / 2 := by norm_num
    rw [e, hu]
    have := abs_sub (z * eval R0 z / eval S0 z) (1 / 4)
    rw [show |(1 / 4 : ℝ)| = 1 / 4 by norm_num] at this
    norm_num
    linarith)
  have ht' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa) - 0.25)
      (z * eval R0 z / eval S0 z - 1 / 4) (37 / 100 * 𝐮) := fmono ht (by rw [hu]; norm_num)
  have htm : |z * eval R0 z / eval S0 z - 1 / 4| ≤ 27 / 100 := by
    have := abs_sub (z * eval R0 z / eval S0 z) (1 / 4)
    rw [show |(1 / 4 : ℝ)| = 1 / 4 by norm_num] at this
    linarith
  have hm := fapprox_mul hz ht' 1 (27 / 100) (by rw [abs_of_nonneg hz0]; exact hv2) htm _ le_rfl
    (by rw [hu]; norm_num)
  have hm' : FApprox (xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa) - 0.25))
      (z * (z * eval R0 z / eval S0 z - 1 / 4)) (92 / 100 * 𝐮) := fmono hm (by rw [hu]; norm_num)
  have hzm : |z * (z * eval R0 z / eval S0 z - 1 / 4)| ≤ 27 / 100 := by
    rw [abs_mul, abs_of_nonneg hz0]; nlinarith [abs_nonneg (z * eval R0 z / eval S0 z - 1 / 4)]
  have hres := fapprox_add_half fapprox_one hm' 1022 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
    rw [e, hu]
    have := abs_add_le (1 : ℝ) (z * (z * eval R0 z / eval S0 z - 1 / 4))
    rw [abs_one] at this
    norm_num
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S0 z ≠ 0 := by linarith
  field_simp
  ring


/-- `(1 + x/2)(1 - x/2) + z (r/s)` for `1 ≤ x < 2`. -/
theorem form2 (xa : Float) (hf : Finite xa.toBits) (hs : Wasm.IEEE64.sign xa.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent xa.toBits) (v : ℝ) (hv : value xa.toBits = v) (h1 : 1 ≤ v)
    (h2 : v < 2) :
    FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0) + xa * xa * (xa * xa *
        hornerF (r0w.map Float.ofBits) (xa * xa) / hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) (4 * 𝐮) := by
  subst hv
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  obtain ⟨-, -, k3, k4, -, -, -, -, -, -, e1, e2, e3, e4, e5, e6⟩ := horner_facts
  set v := value xa.toBits
  have hz := sq_near xa hf 2 (by rw [abs_of_nonneg (by linarith)]; exact h2.le) (by norm_num)
  set z := v ^ 2
  have hz1 : 1 ≤ z := by nlinarith
  have hz4 : z ≤ 4 := by nlinarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (xa * xa) hz.1 z _ lo2 hi2 k3 k4
    (by simp only [lo2]; push_cast; norm_num at hzv ⊢; linarith)
    (by simp only [hi2]; push_cast; norm_num at hzv ⊢; linarith)
    (by simp only [lo2]; push_cast; linarith) (by simp only [hi2]; push_cast; linarith) hz.2
  have hR' : FApprox (hornerF (r0w.map Float.ofBits) (xa * xa)) (eval R0 z) (2 / 100 * 𝐮) := by
    refine fmono hR ?_
    have a1 := (Rat.cast_le (K := ℝ)).mpr e1
    have a2 := (Rat.cast_le (K := ℝ)).mpr e2
    push_cast at a1 a2
    have : (0 : ℝ) ≤ magBound (derivP R0) lo2 hi2 := (abs_nonneg _).trans
      (magBound_sound _ lo2 hi2 1 (by norm_num [lo2]) (by norm_num [hi2]))
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (eval S0 z)
      (127 / 100 * 𝐮) := by
    refine fmono hS ?_
    have a1 := (Rat.cast_le (K := ℝ)).mpr e4
    have a2 := (Rat.cast_le (K := ℝ)).mpr e5
    push_cast at a1 a2
    have : (0 : ℝ) ≤ magBound (derivP S0) lo2 hi2 := (abs_nonneg _).trans
      (magBound_sound _ lo2 hi2 1 (by norm_num [lo2]) (by norm_num [hi2]))
    rw [hu]
    nlinarith
  have hRm : |eval R0 z| ≤ 155 / 10000 := by
    have := magBound_sound R0 lo2 hi2 z (by simp only [lo2]; push_cast; linarith)
      (by simp only [hi2]; push_cast; linarith)
    have a := (Rat.cast_le (K := ℝ)).mpr e3
    push_cast at a
    linarith
  have hSm : 1015 / 1000 ≤ eval S0 z := by
    have := lowBound_sound S0 lo2 hi2 z (by simp only [lo2]; push_cast; linarith)
      (by simp only [hi2]; push_cast; linarith)
    have a := (Rat.cast_le (K := ℝ)).mpr e6
    push_cast at a
    linarith
  have hzR : |z * eval R0 z| ≤ 62 / 1000 := by
    rw [abs_mul, abs_of_nonneg (by linarith)]; nlinarith [abs_nonneg (eval R0 z)]
  have hr := fapprox_mul hz hR' 4 (155 / 10000) (by rw [abs_of_nonneg (by linarith)]; exact hz4)
    hRm _ le_rfl (by rw [hu]; norm_num)
  have hr' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa)) (z * eval R0 z)
      (21 / 100 * 𝐮) := fmono hr (by rw [hu]; norm_num)
  have hq := fapprox_div hr' hS' (62 / 1000) (1015 / 1000) hzR
    (by rw [abs_of_pos (by linarith)]; exact hSm) (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (z * eval R0 z / eval S0 z)
      (35 / 100 * 𝐮) := fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R0 z / eval S0 z| ≤ 62 / 1000 := by
    rw [abs_div, abs_of_pos (show 0 < eval S0 z by linarith), div_le_iff₀ (by linarith)]
    nlinarith
  have hm := fapprox_mul hz hq' 4 (62 / 1000) (by rw [abs_of_nonneg (by linarith)]; exact hz4)
    hqm _ le_rfl (by rw [hu]; norm_num)
  have hm' : FApprox (xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (z * (z * eval R0 z / eval S0 z)) (19 / 10 * 𝐮) := fmono hm (by rw [hu]; norm_num)
  have hzm : |z * (z * eval R0 z / eval S0 z)| ≤ 248 / 1000 := by
    rw [abs_mul, abs_of_nonneg (by linarith)]; nlinarith [abs_nonneg (z * eval R0 z / eval S0 z)]
  -- `x / 2`, `1 + x/2`, `1 - x/2`
  obtain ⟨hwf, hwv⟩ := half_exact xa hf hs he (by linarith)
  have hw : FApprox (xa / 2.0) (v / 2) 0 := ⟨hwf, by rw [hwv]; show |v / 2 - v / 2| ≤ 0; simp⟩
  have hp1 := fapprox_add_half fapprox_one hw 1022 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
    rw [e, abs_of_pos (by linarith)]
    linarith)
  have hp1' : FApprox (1.0 + xa / 2.0) (1 + v / 2) 𝐮 := fmono hp1 (by rw [hu]; norm_num)
  have hone := fapprox_one
  have hm1 : FApprox (1.0 - xa / 2.0) (1 - v / 2) 0 := by
    have hs1 := F64Exact.sub_exact (1.0 : Float).toBits (xa / 2.0).toBits hone.1 hwf
      (by rw [one_bits, value_one]; norm_num) (by rw [hwv]; linarith)
      (by rw [hwv, one_bits, value_one]; linarith) (by rw [hwv, one_bits, value_one]; linarith)
      (by rw [one_bits, value_one]; norm_num) (by rw [hwv]; linarith)
    unfold FApprox Approx
    rw [F64Bits.toBits_sub]
    refine ⟨hs1.1, ?_⟩
    rw [hs1.2, hwv, one_bits, value_one]
    show |1 - v / 2 - (1 - v / 2)| ≤ 0
    simp
  have hp := fapprox_mul hp1' hm1 2 (1 / 2) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0)) ((1 + v / 2) * (1 - v / 2))
      (151 / 100 * 𝐮) := fmono hp (by rw [hu]; norm_num)
  have hpm : |(1 + v / 2) * (1 - v / 2)| ≤ 3 / 4 := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hres := fapprox_add_half hp' hm' 1021 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1021) / 2 ^ 1074 = 1 := by norm_num
    rw [e, hu]
    have := abs_add_le ((1 + v / 2) * (1 - v / 2)) (z * (z * eval R0 z / eval S0 z))
    norm_num
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S0 z ≠ 0 := by linarith
  field_simp
  ring

/-- `J₀ x = 1 - x²/4` up to `x⁴/32` for `|x| ≤ 2`. -/
theorem j0_quad (v : ℝ) (hv : |v| ≤ 2) : |J0 v - (1 - v ^ 2 / 4)| ≤ v ^ 4 / 32 := by
  obtain ⟨-, -, -, -, -, -, -, -, q0, q1, q2, -⟩ := coeff_facts
  obtain ⟨hz0, hz1⟩ := zeta_facts v hv
  have hr := a0_remainder (v ^ 2 / 4) (by rw [abs_of_nonneg hz0]; exact hz1) 2 (by norm_num)
  have e : eval (a0List 2) (v ^ 2 / 4) = 1 - v ^ 2 / 4 := by
    simp only [a0List, List.range_succ, List.range_zero, List.nil_append, List.cons_append,
      List.map_cons, List.map_nil, eval_cons, eval_nil]
    rw [q0, q1]
    push_cast
    ring
  have ha : |a0 2| = 1 / 4 := by rw [a0, ← qabs_cast, q2]; norm_num
  rw [e, ha, abs_of_nonneg hz0] at hr
  have : J0 v = psum a0 (v ^ 2 / 4) := rfl
  rw [this]
  calc _ ≤ 2 * (1 / 4) * (v ^ 2 / 4) ^ 2 := hr
    _ = v ^ 4 / 32 := by ring

theorem flt_iff (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a < b ↔ value a.toBits < value b.toBits := by
  rw [F64Bits.lt_iff]
  unfold Wasm.IEEE64.lt
  rw [not_nan_of_finite ha, not_nan_of_finite hb, TrigSmall.value_of_scaled,
    TrigSmall.value_of_scaled]
  simp only [Bool.or_false, Bool.false_eq_true, ite_false, decide_eq_true_eq]
  constructor
  · intro h
    exact div_lt_div_of_pos_right (by exact_mod_cast h) (by positivity)
  · intro h
    have := (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1074)).mp h
    exact_mod_cast this

/-- `1e300 + x > 1` for `0 ≤ x ≤ 2`. -/
theorem huge_add (xa : Float) (hf : Finite xa.toBits) (h0 : 0 ≤ value xa.toBits)
    (h2 : value xa.toBits ≤ 2) : Float.ofBits 0x7E37E43C8800759C + xa > 1.0 := by
  have hc : FApprox (Float.ofBits 0x7E37E43C8800759C) (ratOfWord 0x7E37E43C8800759C) 0 := by
    have := fapprox_ofBits 0x7E37E43C8800759C (by unfold CodeLib.IEEE64.Finite; decide)
    rw [← ratOfWord_cast] at this
    exact this
  have hb : (2 : ℚ) ^ 996 ≤ ratOfWord 0x7E37E43C8800759C ∧
      ratOfWord 0x7E37E43C8800759C ≤ 2 ^ 997 := by decide +kernel
  have b1 := (Rat.cast_le (K := ℝ)).mpr hb.1
  have b2 := (Rat.cast_le (K := ℝ)).mpr hb.2
  push_cast at b1 b2
  have hs := fapprox_add hc (fapprox_exact xa hf) (2 ^ 998) (by
    rw [abs_of_nonneg (by linarith)]
    have : (2 : ℝ) ^ 997 + 2 ≤ 2 ^ 998 := by norm_num
    linarith) (by norm_num)
  rw [gt_iff_lt, flt_iff _ _ fapprox_one.1 hs.1, one_bits, value_one]
  have := (abs_le.mp hs.2).1
  have e : (2 : ℝ) ^ 996 - (0 + 0 + 2 ^ 998 / 2 ^ 53) > 1 := by norm_num
  linarith

/-- `j0` for `|x| < 2`. -/
theorem j0_small (x : Float) (hxf : Finite x.toBits)
    (h2 : x.toBits.toNat % 2 ^ 63 < 0x4000000000000000) :
    Finite (Bessel.j0 x).toBits ∧
      |value (Bessel.j0 x).toBits - J0 (value x.toBits)| ≤ 42 / 10 * 𝐮 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hab := F64Bits.toBits_abs x
  have hN := TrigSinCos.abs_toNat x.toBits
  have haf : Finite x.abs.toBits := by rw [hab]; exact TrigSinCos.abs_finite _ hxf
  have hav : value x.abs.toBits = |value x.toBits| := by rw [hab, TrigSinCos.abs_value]
  have haN : x.abs.toBits.toNat = x.toBits.toNat % 2 ^ 63 := by rw [hab, hN]
  have hs : Wasm.IEEE64.sign x.abs.toBits = false := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le]
    rw [haN]; omega
  have hJ : J0 (value x.toBits) = J0 |value x.toBits| := by unfold J0; rw [sq_abs]
  rw [hJ, ← hav]
  set w := value x.abs.toBits with hw
  have hw0 : 0 ≤ w := by rw [hav]; exact abs_nonneg _
  have hw2 : w < 2 := by
    have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
      (right := (0x4000000000000000 : UInt64)) (by decide) (by rw [haN]; exact h2)
    rw [value_two] at h
    exact h
  have hixN := TrigSinCos.high_word x.toBits
  have hfin := TrigSinCos.finite_bound x.toBits hxf
  unfold Bessel.j0 Bessel.j0With
  dsimp only
  rw [ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 2146435072) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega),
    ite_eq_right (show ¬ (x.toBits >>> 32 &&& 2147483647 ≥ 1073741824) by
      rw [ge_iff_le, UInt64.le_iff_toNat_le, hixN]; simp only [UInt64.reduceToNat]; omega)]
  have hbig := huge_add x.abs haf hw0 hw2.le
  by_cases h13 : x.toBits >>> 32 &&& 2147483647 < 1059061760
  · rw [ite_eq_left (by simp [h13, hbig])]
    by_cases h27 : x.toBits >>> 32 &&& 2147483647 < 1044381696
    · rw [ite_eq_left h27, one_bits, value_one]
      refine ⟨by unfold CodeLib.IEEE64.Finite; decide, ?_⟩
      have hsmall : w < 1 / 2 ^ 27 := by
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
        rw [e] at h
        exact h
      have hq := j0_quad w (by rw [abs_of_nonneg hw0]; linarith)
      have h2' : w ^ 2 ≤ 1 / 2 ^ 54 := by
        have := pow_le_pow_left₀ hw0 hsmall.le 2
        norm_num at this ⊢
        linarith
      have h4 : w ^ 4 ≤ 1 / 2 ^ 108 := by
        have := pow_le_pow_left₀ (by positivity) h2' 2
        rw [← pow_mul] at this
        norm_num at this ⊢
        linarith
      rw [abs_sub_comm]
      have := abs_sub_le (J0 w) (1 - w ^ 2 / 4) 1
      rw [show |1 - w ^ 2 / 4 - 1| = w ^ 2 / 4 by
        rw [show 1 - w ^ 2 / 4 - 1 = -(w ^ 2 / 4) by ring, abs_neg, abs_of_nonneg (by positivity)]]
        at this
      rw [hu]
      norm_num at hq h2' h4 ⊢
      linarith
    · rw [ite_eq_right h27]
      have hsmall : w < 1 / 2 ^ 13 := by
        have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
          (right := (0x3F20000000000000 : UInt64)) (by decide) (by
            rw [haN]
            simp only [UInt64.reduceToNat]
            have := UInt64.lt_iff_toNat_lt.mp h13
            rw [hixN] at this
            simp only [UInt64.reduceToNat] at this
            omega)
        have e : value (0x3F20000000000000 : UInt64) = 1 / 2 ^ 13 := by
          rw [← ratOfWord_cast]
          have : ratOfWord 0x3F20000000000000 = 1 / 2 ^ 13 := by decide +kernel
          rw [this]; norm_num
        rw [e] at h
        exact h
      have hz := sq_near x.abs haf (1 / 2 ^ 13) (by rw [abs_of_nonneg hw0]; exact hsmall.le)
        (by norm_num)
      have hfour : FApprox (4.0 : Float) 4 0 := by
        unfold FApprox Approx
        have hb4 : (4.0 : Float).toBits = 0x4010000000000000 := rfl
        rw [hb4, ← ratOfWord_cast]
        have : ratOfWord 0x4010000000000000 = 4 := by decide +kernel
        rw [this]
        exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by norm_num⟩
      have hw2' : |w ^ 2| ≤ 1 / 2 ^ 26 := by
        rw [abs_of_nonneg (by positivity)]
        have := pow_le_pow_left₀ hw0 hsmall.le 2
        norm_num at this ⊢
        linarith
      have hq := fapprox_div hz hfour (1 / 2 ^ 26) 4 hw2' (by norm_num) (by norm_num) _ le_rfl
        (by norm_num)
      have hres := fapprox_sub_half fapprox_one hq 1022 (by norm_num) (by
        have e : (2 : ℝ) ^ (53 + 1022) / 2 ^ 1074 = 2 := by norm_num
        rw [e]
        have : |1 - w ^ 2 / 4| ≤ 1 := by
          rw [abs_le]; constructor <;> nlinarith
        norm_num at this ⊢
        linarith)
      refine ⟨hres.1, ?_⟩
      have hq2 := j0_quad w (by rw [abs_of_nonneg hw0]; linarith)
      have h4 : w ^ 4 ≤ 1 / 2 ^ 52 := by
        have := pow_le_pow_left₀ (by positivity) (abs_le.mp hw2').2 2
        rw [abs_of_nonneg (by positivity)] at hw2'
        rw [← pow_mul] at this
        norm_num at this ⊢
        linarith
      have := abs_sub_le (value (1.0 - x.abs * x.abs / 4.0).toBits) (1 - w ^ 2 / 4) (J0 w)
      rw [abs_sub_comm (1 - w ^ 2 / 4)] at this
      have h3 := hres.2
      rw [hu]
      norm_num at h3 hq2 h4 ⊢
      linarith
  · rw [ite_eq_right (by simp [h13])]
    have h13' : 1 / 2 ^ 13 ≤ w := by
      have h := (F64PositiveOrder.value_le_iff (left := (0x3F20000000000000 : UInt64))
        (right := x.abs.toBits) (by decide) (by rw [haN]; omega)).mpr (by
          rw [haN]
          simp only [UInt64.reduceToNat]
          have : ¬ (1059061760 : UInt64).toNat > (x.toBits >>> 32 &&& 2147483647).toNat :=
            fun h => h13 (UInt64.lt_iff_toNat_lt.mpr h)
          rw [hixN] at this
          simp only [UInt64.reduceToNat] at this
          omega)
      have e : value (0x3F20000000000000 : UInt64) = 1 / 2 ^ 13 := by
        rw [← ratOfWord_cast]
        have : ratOfWord 0x3F20000000000000 = 1 / 2 ^ 13 := by decide +kernel
        rw [this]; norm_num
      rw [e] at h
      exact h
    have hap := j0_approx w (by rw [abs_of_nonneg hw0]; linarith)
    by_cases h1 : x.toBits >>> 32 &&& 2147483647 < 1072693248
    · rw [ite_eq_left h1]
      have hw1 : w ≤ 1 := by
        have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
          (right := (0x3FF0000000000000 : UInt64)) (by decide) (by
            rw [haN]
            simp only [UInt64.reduceToNat]
            have := UInt64.lt_iff_toNat_lt.mp h1
            rw [hixN] at this
            simp only [UInt64.reduceToNat] at this
            omega)
        rw [value_one] at h
        exact h.le
      have hf1 := form1 x.abs haf w hw.symm hw0 hw1
      refine ⟨hf1.1, ?_⟩
      show |value (1.0 + x.abs * x.abs * (x.abs * x.abs *
        hornerF (r0w.map Float.ofBits) (x.abs * x.abs) /
        hornerF (1.0 :: s0w.map Float.ofBits) (x.abs * x.abs) - 0.25)).toBits - J0 w| ≤ _
      have := abs_sub_le (value (1.0 + x.abs * x.abs * (x.abs * x.abs *
        hornerF (r0w.map Float.ofBits) (x.abs * x.abs) /
        hornerF (1.0 :: s0w.map Float.ofBits) (x.abs * x.abs) - 0.25)).toBits)
        (1 - w ^ 2 / 4 + w ^ 2 * (w ^ 2 * eval R0 (w ^ 2)) / eval S0 (w ^ 2)) (J0 w)
      rw [abs_sub_comm (1 - w ^ 2 / 4 + _)] at this
      have h3 := hf1.2
      rw [hu] at h3 hap ⊢
      norm_num at hap h3 ⊢
      linarith
    · rw [ite_eq_right h1]
      have hw1 : 1 ≤ w := by
        have h := (F64PositiveOrder.value_le_iff (left := (0x3FF0000000000000 : UInt64))
          (right := x.abs.toBits) (by decide) (by rw [haN]; omega)).mpr (by
            rw [haN]
            simp only [UInt64.reduceToNat]
            have : ¬ (1072693248 : UInt64).toNat > (x.toBits >>> 32 &&& 2147483647).toNat :=
              fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h)
            rw [hixN] at this
            simp only [UInt64.reduceToNat] at this
            omega)
        rw [value_one] at h
        exact h
      have he : 2 ≤ Wasm.IEEE64.exponent x.abs.toBits := by
        simp only [Wasm.IEEE64.exponent]
        rw [haN]
        have : ¬ (1072693248 : UInt64).toNat > (x.toBits >>> 32 &&& 2147483647).toNat :=
          fun h => h1 (UInt64.lt_iff_toNat_lt.mpr h)
        rw [hixN] at this
        simp only [UInt64.reduceToNat] at this
        omega
      have hf2 := form2 x.abs haf hs he w hw.symm hw1 hw2
      refine ⟨hf2.1, ?_⟩
      show |value ((1.0 + x.abs / 2.0) * (1.0 - x.abs / 2.0) + x.abs * x.abs *
        (x.abs * x.abs * hornerF (r0w.map Float.ofBits) (x.abs * x.abs) /
        hornerF (1.0 :: s0w.map Float.ofBits) (x.abs * x.abs))).toBits - J0 w| ≤ _
      have := abs_sub_le (value ((1.0 + x.abs / 2.0) * (1.0 - x.abs / 2.0) + x.abs * x.abs *
        (x.abs * x.abs * hornerF (r0w.map Float.ofBits) (x.abs * x.abs) /
        hornerF (1.0 :: s0w.map Float.ofBits) (x.abs * x.abs))).toBits)
        (1 - w ^ 2 / 4 + w ^ 2 * (w ^ 2 * eval R0 (w ^ 2)) / eval S0 (w ^ 2)) (J0 w)
      rw [abs_sub_comm (1 - w ^ 2 / 4 + _)] at this
      have h3 := hf2.2
      rw [hu] at h3 hap ⊢
      norm_num at hap h3 ⊢
      linarith

#print axioms horner_facts
#print axioms form1
#print axioms form2
#print axioms j0_quad
#print axioms flt_iff
#print axioms huge_add
#print axioms j0_small

end Verified.Examples.BesselSmallJ0
