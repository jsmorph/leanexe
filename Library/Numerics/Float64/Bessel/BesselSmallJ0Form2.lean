import Library.Numerics.Float64.Bessel.BesselSmallJ0

/-!
The second form of `Bessel.j0`, `(1 + x/2)(1 - x/2) + z (z R(z)/S(z))` with `z = x x`, which the
code takes for `1 ≤ |x| < 2`.  Each lemma `form2_k` follows it through `F64Approx` on one range of
`|x|`, with the Horner bounds that the kernel checks on that range (`facts2_k`), the exact `x/2` of
`BesselSmallEval.half_exact`, and the exact `1 - x/2` of Sterbenz's lemma; this file is generated
by `tools/bessel/gensmall.py`.
-/

namespace Library.Numerics.Float64.Bessel.BesselSmallJ0Form2
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound PolyCalculus F64Approx F64HalfUlp F64Horner
  BesselPQEval BesselPQRange BesselCS BesselSmallEval BesselSmallApprox BesselJ0Large BesselSmallJ0
open LeanExe.ProofKit.Bessel LeanExe.ProofKit.EntireSeries

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

theorem facts2_0 : hornerOK R0 (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) = true ∧ hornerOK S0 (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) = true ∧
    hornerErr R0 (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (8017 / 4503599627370496000000 : ℚ) ∧ magBound (derivP R0) (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (187 / 1000000 : ℚ) ∧
    magBound R0 (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (15437 / 1000000 : ℚ) ∧ hornerErr S0 (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (33583 / 281474976710656000000 : ℚ) ∧
    magBound (derivP S0) (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) ≤ (15989 / 1000000 : ℚ) ∧ (1015717 / 1000000 : ℚ) ≤ lowBound S0 (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) := by
  decide +kernel

/-- The second form of `j0` for `1 ≤ x ≤ 5/4`. -/
theorem form2_0 (xa : Float) (hf : Finite xa.toBits) (hs : Wasm.IEEE64.sign xa.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent xa.toBits) (v : ℝ) (hv : value xa.toBits = v) (ha : (1 : ℝ) ≤ v)
    (hb : v ≤ (5 / 4 : ℝ)) (hlt : v < 2) :
    FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0) + xa * xa * (xa * xa *
        hornerF (r0w.map Float.ofBits) (xa * xa) / hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) ((2081 / 1000 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts2_0
  subst hv
  set v := value xa.toBits
  have hz := sq_near xa hf (5 / 4 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (1 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (5 / 4 : ℝ) ^ 2 := by nlinarith
  have hzm : |z| ≤ (25 / 16 : ℝ) := by
    rw [abs_of_nonneg (by rw [hzd]; positivity)]; norm_num at hzb ⊢; linarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (xa * xa) hz.1 z _ (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP R0) (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP S0) (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (r0w.map Float.ofBits) (xa * xa)) (eval R0 z) ((17 / 1000 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (eval S0 z) ((11 / 10 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval R0 z| ≤ (15437 / 1000000 : ℝ) := (magBound_sound R0 (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (1015717 / 1000000 : ℝ) ≤ |eval S0 z| := by
    have := (lowBound_sound S0 (1125899906842623 / 1125899906842624 : ℚ) (28147497671065625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hr := fapprox_mul hz hH (25 / 16 : ℝ) (15437 / 1000000 : ℝ) hzm hHm _ le_rfl (by rw [hu]; norm_num)
  have hr' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa)) (z * eval R0 z) ((3 / 40 : ℝ) * 𝐮) :=
    fmono hr (by rw [hu]; norm_num)
  have hrm : |z * eval R0 z| ≤ (15437 / 640000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hHm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hq := fapprox_div hr' hS' (15437 / 640000 : ℝ) (1015717 / 1000000 : ℝ) hrm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (z * eval R0 z / eval S0 z) ((31 / 250 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R0 z / eval S0 z| ≤ (5937 / 250000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hrm (by norm_num) hSm).trans (by norm_num)
  have hm := fapprox_mul hz hq' (25 / 16 : ℝ) (5937 / 250000 : ℝ) hzm hqm _ le_rfl (by rw [hu]; norm_num)
  have hm' : FApprox (xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa))) (z * (z * eval R0 z / eval S0 z)) ((67 / 250 : ℝ) * 𝐮) :=
    fmono hm (by rw [hu]; norm_num)
  have hmm : |z * (z * eval R0 z / eval S0 z)| ≤ (37107 / 1000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
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
  have hp := fapprox_mul hp1' hm1 (13 / 8 : ℝ) (1 / 2 : ℝ) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0)) ((1 + v / 2) * (1 - v / 2)) ((1313 / 1000 : ℝ) * 𝐮) :=
    fmono hp (by rw [hu]; norm_num)
  have hpm : |(1 + v / 2) * (1 - v / 2)| ≤ (3 / 4 : ℝ) := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hres := fapprox_add_half hp' hm' 1021 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1021) / 2 ^ 1074 = (1 : ℝ) := by norm_num
    rw [e]
    have h1 := abs_add_le ((1 + v / 2) * (1 - v / 2)) (z * (z * eval R0 z / eval S0 z))
    have h2 : (1313 / 1000 : ℝ) * 𝐮 + (67 / 250 : ℝ) * 𝐮 < (1 : ℝ) - ((3 / 4 : ℝ) + (37107 / 1000000 : ℝ)) := by rw [hu]; norm_num
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S0 z ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hSm; norm_num at hSm
  field_simp
  ring

theorem facts2_1 : hornerOK R0 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) = true ∧ hornerOK S0 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) = true ∧
    hornerErr R0 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (8097 / 4503599627370496000000 : ℚ) ∧ magBound (derivP R0) (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (37 / 200000 : ℚ) ∧
    magBound R0 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (15333 / 1000000 : ℚ) ∧ hornerErr S0 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (110843 / 900719925474099200000 : ℚ) ∧
    magBound (derivP S0) (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) ≤ (8077 / 500000 : ℚ) ∧ (1024663 / 1000000 : ℚ) ≤ lowBound S0 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) := by
  decide +kernel

/-- The second form of `j0` for `5/4 ≤ x ≤ 3/2`. -/
theorem form2_1 (xa : Float) (hf : Finite xa.toBits) (hs : Wasm.IEEE64.sign xa.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent xa.toBits) (v : ℝ) (hv : value xa.toBits = v) (ha : (5 / 4 : ℝ) ≤ v)
    (hb : v ≤ (3 / 2 : ℝ)) (hlt : v < 2) :
    FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0) + xa * xa * (xa * xa *
        hornerF (r0w.map Float.ofBits) (xa * xa) / hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) ((1041 / 500 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts2_1
  subst hv
  set v := value xa.toBits
  have hz := sq_near xa hf (3 / 2 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (5 / 4 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (3 / 2 : ℝ) ^ 2 := by nlinarith
  have hzm : |z| ≤ (9 / 4 : ℝ) := by
    rw [abs_of_nonneg (by rw [hzd]; positivity)]; norm_num at hzb ⊢; linarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (xa * xa) hz.1 z _ (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP R0) (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP S0) (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (r0w.map Float.ofBits) (xa * xa)) (eval R0 z) ((17 / 1000 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (eval S0 z) ((229 / 200 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval R0 z| ≤ (15333 / 1000000 : ℝ) := (magBound_sound R0 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (1024663 / 1000000 : ℝ) ≤ |eval S0 z| := by
    have := (lowBound_sound S0 (28147497671065575 / 18014398509481984 : ℚ) (10133099161583625 / 4503599627370496 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hr := fapprox_mul hz hH (9 / 4 : ℝ) (15333 / 1000000 : ℝ) hzm hHm _ le_rfl (by rw [hu]; norm_num)
  have hr' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa)) (z * eval R0 z) ((27 / 250 : ℝ) * 𝐮) :=
    fmono hr (by rw [hu]; norm_num)
  have hrm : |z * eval R0 z| ≤ (137997 / 4000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hHm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hq := fapprox_div hr' hS' (137997 / 4000000 : ℝ) (1024663 / 1000000 : ℝ) hrm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (z * eval R0 z / eval S0 z) ((177 / 1000 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R0 z / eval S0 z| ≤ (33669 / 1000000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hrm (by norm_num) hSm).trans (by norm_num)
  have hm := fapprox_mul hz hq' (9 / 4 : ℝ) (33669 / 1000000 : ℝ) hzm hqm _ le_rfl (by rw [hu]; norm_num)
  have hm' : FApprox (xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa))) (z * (z * eval R0 z / eval S0 z)) ((11 / 20 : ℝ) * 𝐮) :=
    fmono hm (by rw [hu]; norm_num)
  have hmm : |z * (z * eval R0 z / eval S0 z)| ≤ (18939 / 250000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
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
  have hp := fapprox_mul hp1' hm1 (7 / 4 : ℝ) (3 / 8 : ℝ) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0)) ((1 + v / 2) * (1 - v / 2)) ((129 / 125 : ℝ) * 𝐮) :=
    fmono hp (by rw [hu]; norm_num)
  have hpm : |(1 + v / 2) * (1 - v / 2)| ≤ (39 / 64 : ℝ) := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hres := fapprox_add_half hp' hm' 1021 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1021) / 2 ^ 1074 = (1 : ℝ) := by norm_num
    rw [e]
    have h1 := abs_add_le ((1 + v / 2) * (1 - v / 2)) (z * (z * eval R0 z / eval S0 z))
    have h2 : (129 / 125 : ℝ) * 𝐮 + (11 / 20 : ℝ) * 𝐮 < (1 : ℝ) - ((39 / 64 : ℝ) + (18939 / 250000 : ℝ)) := by rw [hu]; norm_num
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S0 z ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hSm; norm_num at hSm
  field_simp
  ring

theorem facts2_2 : hornerOK R0 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) = true ∧ hornerOK S0 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) = true ∧
    hornerErr R0 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (819 / 450359962737049600000 : ℚ) ∧ magBound (derivP R0) (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (91 / 500000 : ℚ) ∧
    magBound R0 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (15207 / 1000000 : ℚ) ∧ hornerErr S0 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (35909 / 281474976710656000000 : ℚ) ∧
    magBound (derivP S0) (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) ≤ (327 / 20000 : ℚ) ∧ (10357 / 10000 : ℚ) ≤ lowBound S0 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) := by
  decide +kernel

/-- The second form of `j0` for `3/2 ≤ x ≤ 7/4`. -/
theorem form2_2 (xa : Float) (hf : Finite xa.toBits) (hs : Wasm.IEEE64.sign xa.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent xa.toBits) (v : ℝ) (hv : value xa.toBits = v) (ha : (3 / 2 : ℝ) ≤ v)
    (hb : v ≤ (7 / 4 : ℝ)) (hlt : v < 2) :
    FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0) + xa * xa * (xa * xa *
        hornerF (r0w.map Float.ofBits) (xa * xa) / hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) ((2227 / 1000 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts2_2
  subst hv
  set v := value xa.toBits
  have hz := sq_near xa hf (7 / 4 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (3 / 2 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (7 / 4 : ℝ) ^ 2 := by nlinarith
  have hzm : |z| ≤ (49 / 16 : ℝ) := by
    rw [abs_of_nonneg (by rw [hzd]; positivity)]; norm_num at hzb ⊢; linarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (xa * xa) hz.1 z _ (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP R0) (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP S0) (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (r0w.map Float.ofBits) (xa * xa)) (eval R0 z) ((17 / 1000 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (eval S0 z) ((6 / 5 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval R0 z| ≤ (15207 / 1000000 : ℝ) := (magBound_sound R0 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (10357 / 10000 : ℝ) ≤ |eval S0 z| := by
    have := (lowBound_sound S0 (10133099161583607 / 4503599627370496 : ℚ) (55169095435288625 / 18014398509481984 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hr := fapprox_mul hz hH (49 / 16 : ℝ) (15207 / 1000000 : ℝ) hzm hHm _ le_rfl (by rw [hu]; norm_num)
  have hr' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa)) (z * eval R0 z) ((73 / 500 : ℝ) * 𝐮) :=
    fmono hr (by rw [hu]; norm_num)
  have hrm : |z * eval R0 z| ≤ (745143 / 16000000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hHm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hq := fapprox_div hr' hS' (745143 / 16000000 : ℝ) (10357 / 10000 : ℝ) hrm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (z * eval R0 z / eval S0 z) ((239 / 1000 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R0 z / eval S0 z| ≤ (44967 / 1000000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hrm (by norm_num) hSm).trans (by norm_num)
  have hm := fapprox_mul hz hq' (49 / 16 : ℝ) (44967 / 1000000 : ℝ) hzm hqm _ le_rfl (by rw [hu]; norm_num)
  have hm' : FApprox (xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa))) (z * (z * eval R0 z / eval S0 z)) ((126 / 125 : ℝ) * 𝐮) :=
    fmono hm (by rw [hu]; norm_num)
  have hmm : |z * (z * eval R0 z / eval S0 z)| ≤ (8607 / 62500 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
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
  have hp := fapprox_mul hp1' hm1 (15 / 8 : ℝ) (1 / 4 : ℝ) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0)) ((1 + v / 2) * (1 - v / 2)) ((719 / 1000 : ℝ) * 𝐮) :=
    fmono hp (by rw [hu]; norm_num)
  have hpm : |(1 + v / 2) * (1 - v / 2)| ≤ (7 / 16 : ℝ) := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hres := fapprox_add_half hp' hm' 1021 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1021) / 2 ^ 1074 = (1 : ℝ) := by norm_num
    rw [e]
    have h1 := abs_add_le ((1 + v / 2) * (1 - v / 2)) (z * (z * eval R0 z / eval S0 z))
    have h2 : (719 / 1000 : ℝ) * 𝐮 + (126 / 125 : ℝ) * 𝐮 < (1 : ℝ) - ((7 / 16 : ℝ) + (8607 / 62500 : ℝ)) := by rw [hu]; norm_num
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S0 z ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hSm; norm_num at hSm
  field_simp
  ring

theorem facts2_3 : hornerOK R0 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) = true ∧ hornerOK S0 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) = true ∧
    hornerErr R0 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (8201 / 4503599627370496000000 : ℚ) ∧ magBound (derivP R0) (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (179 / 1000000 : ℚ) ∧
    magBound R0 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (15061 / 1000000 : ℚ) ∧ hornerErr S0 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (1172117 / 9007199254740992000000 : ℚ) ∧
    magBound (derivP S0) (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) ≤ (16461 / 1000000 : ℚ) ∧ (262233 / 250000 : ℚ) ≤ lowBound S0 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) := by
  decide +kernel

/-- The second form of `j0` for `7/4 ≤ x ≤ 15/8`. -/
theorem form2_3 (xa : Float) (hf : Finite xa.toBits) (hs : Wasm.IEEE64.sign xa.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent xa.toBits) (v : ℝ) (hv : value xa.toBits = v) (ha : (7 / 4 : ℝ) ≤ v)
    (hb : v ≤ (15 / 8 : ℝ)) (hlt : v < 2) :
    FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0) + xa * xa * (xa * xa *
        hornerF (r0w.map Float.ofBits) (xa * xa) / hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) ((193 / 100 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts2_3
  subst hv
  set v := value xa.toBits
  have hz := sq_near xa hf (15 / 8 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (7 / 4 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (15 / 8 : ℝ) ^ 2 := by nlinarith
  have hzm : |z| ≤ (225 / 64 : ℝ) := by
    rw [abs_of_nonneg (by rw [hzd]; positivity)]; norm_num at hzb ⊢; linarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (xa * xa) hz.1 z _ (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP R0) (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP S0) (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (r0w.map Float.ofBits) (xa * xa)) (eval R0 z) ((9 / 500 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (eval S0 z) ((123 / 100 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval R0 z| ≤ (15061 / 1000000 : ℝ) := (magBound_sound R0 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (262233 / 250000 : ℝ) ≤ |eval S0 z| := by
    have := (lowBound_sound S0 (55169095435288527 / 18014398509481984 : ℚ) (253327479039590625 / 72057594037927936 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hr := fapprox_mul hz hH (225 / 64 : ℝ) (15061 / 1000000 : ℝ) hzm hHm _ le_rfl (by rw [hu]; norm_num)
  have hr' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa)) (z * eval R0 z) ((17 / 100 : ℝ) * 𝐮) :=
    fmono hr (by rw [hu]; norm_num)
  have hrm : |z * eval R0 z| ≤ (135549 / 2560000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hHm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hq := fapprox_div hr' hS' (135549 / 2560000 : ℝ) (262233 / 250000 : ℝ) hrm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (z * eval R0 z / eval S0 z) ((34 / 125 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R0 z / eval S0 z| ≤ (50479 / 1000000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hrm (by norm_num) hSm).trans (by norm_num)
  have hm := fapprox_mul hz hq' (225 / 64 : ℝ) (50479 / 1000000 : ℝ) hzm hqm _ le_rfl (by rw [hu]; norm_num)
  have hm' : FApprox (xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa))) (z * (z * eval R0 z / eval S0 z)) ((164 / 125 : ℝ) * 𝐮) :=
    fmono hm (by rw [hu]; norm_num)
  have hmm : |z * (z * eval R0 z / eval S0 z)| ≤ (88733 / 500000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
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
  have hp := fapprox_mul hp1' hm1 (31 / 16 : ℝ) (1 / 8 : ℝ) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0)) ((1 + v / 2) * (1 - v / 2)) ((46 / 125 : ℝ) * 𝐮) :=
    fmono hp (by rw [hu]; norm_num)
  have hpm : |(1 + v / 2) * (1 - v / 2)| ≤ (15 / 64 : ℝ) := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hres := fapprox_add_half hp' hm' 1020 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1020) / 2 ^ 1074 = (1 / 2 : ℝ) := by norm_num
    rw [e]
    have h1 := abs_add_le ((1 + v / 2) * (1 - v / 2)) (z * (z * eval R0 z / eval S0 z))
    have h2 : (46 / 125 : ℝ) * 𝐮 + (164 / 125 : ℝ) * 𝐮 < (1 / 2 : ℝ) - ((15 / 64 : ℝ) + (88733 / 500000 : ℝ)) := by rw [hu]; norm_num
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S0 z ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hSm; norm_num at hSm
  field_simp
  ring

theorem facts2_4 : hornerOK R0 (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) = true ∧ hornerOK S0 (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) = true ∧
    hornerErr R0 (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (16507 / 9007199254740992000000 : ℚ) ∧ magBound (derivP R0) (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (89 / 500000 : ℚ) ∧
    magBound R0 (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (749 / 50000 : ℚ) ∧ hornerErr S0 (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (149627 / 1125899906842624000000 : ℚ) ∧
    magBound (derivP S0) (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) ≤ (829 / 50000 : ℚ) ∧ (264091 / 250000 : ℚ) ≤ lowBound S0 (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) := by
  decide +kernel

/-- The second form of `j0` for `15/8 ≤ x ≤ 2`. -/
theorem form2_4 (xa : Float) (hf : Finite xa.toBits) (hs : Wasm.IEEE64.sign xa.toBits = false)
    (he : 2 ≤ Wasm.IEEE64.exponent xa.toBits) (v : ℝ) (hv : value xa.toBits = v) (ha : (15 / 8 : ℝ) ≤ v)
    (hb : v ≤ (2 : ℝ)) (hlt : v < 2) :
    FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0) + xa * xa * (xa * xa *
        hornerF (r0w.map Float.ofBits) (xa * xa) / hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)))
      (1 - v ^ 2 / 4 + v ^ 2 * (v ^ 2 * eval R0 (v ^ 2)) / eval S0 (v ^ 2)) ((53 / 25 : ℝ) * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  obtain ⟨k1, k2, e1, e2, e3, e4, e5, e6⟩ := facts2_4
  subst hv
  set v := value xa.toBits
  have hz := sq_near xa hf (2 : ℝ) (by rw [abs_of_nonneg (by linarith)]; exact hb) (by norm_num)
  set z := v ^ 2 with hzd
  have hza : (15 / 8 : ℝ) ^ 2 ≤ z := by nlinarith
  have hzb : z ≤ (2 : ℝ) ^ 2 := by nlinarith
  have hzm : |z| ≤ (4 : ℝ) := by
    rw [abs_of_nonneg (by rw [hzd]; positivity)]; norm_num at hzb ⊢; linarith
  have hzv := abs_le.mp hz.2
  obtain ⟨hR, hS⟩ := rs_at (xa * xa) hz.1 z _ (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) k1 k2
    (by push_cast; norm_num at hzv hza ⊢; linarith) (by push_cast; norm_num at hzv hzb ⊢; linarith)
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith) hz.2
  have a1 := (Rat.cast_le (K := ℝ)).mpr e1
  have a2 := (Rat.cast_le (K := ℝ)).mpr e2
  have a3 := (Rat.cast_le (K := ℝ)).mpr e3
  have a4 := (Rat.cast_le (K := ℝ)).mpr e4
  have a5 := (Rat.cast_le (K := ℝ)).mpr e5
  have a6 := (Rat.cast_le (K := ℝ)).mpr e6
  have hL1 : (0 : ℝ) ≤ magBound (derivP R0) (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  have hL2 : (0 : ℝ) ≤ magBound (derivP S0) (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) := (abs_nonneg _).trans
    (magBound_sound _ (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
  push_cast at a1 a2 a3 a4 a5 a6
  have hH : FApprox (hornerF (r0w.map Float.ofBits) (xa * xa)) (eval R0 z) ((9 / 500 : ℝ) * 𝐮) := by
    refine fmono hR ?_
    rw [hu]
    nlinarith
  have hS' : FApprox (hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (eval S0 z) ((158 / 125 : ℝ) * 𝐮) := by
    refine fmono hS ?_
    rw [hu]
    nlinarith
  have hHm : |eval R0 z| ≤ (749 / 50000 : ℝ) := (magBound_sound R0 (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) z
    (by push_cast; norm_num at hza ⊢; linarith) (by push_cast; norm_num at hzb ⊢; linarith)).trans a3
  have hSm : (264091 / 250000 : ℝ) ≤ |eval S0 z| := by
    have := (lowBound_sound S0 (253327479039590175 / 72057594037927936 : ℚ) (1125899906842625 / 281474976710656 : ℚ) z (by push_cast; norm_num at hza ⊢; linarith)
      (by push_cast; norm_num at hzb ⊢; linarith))
    rw [abs_of_pos (by linarith)]
    linarith
  have hr := fapprox_mul hz hH (4 : ℝ) (749 / 50000 : ℝ) hzm hHm _ le_rfl (by rw [hu]; norm_num)
  have hr' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa)) (z * eval R0 z) ((24 / 125 : ℝ) * 𝐮) :=
    fmono hr (by rw [hu]; norm_num)
  have hrm : |z * eval R0 z| ≤ (749 / 12500 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hHm (abs_nonneg _) (by norm_num)).trans (by norm_num)
  have hq := fapprox_div hr' hS' (749 / 12500 : ℝ) (264091 / 250000 : ℝ) hrm hSm (by rw [hu]; norm_num) _ le_rfl
    (by rw [hu]; norm_num)
  have hq' : FApprox (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa)) (z * eval R0 z / eval S0 z) ((307 / 1000 : ℝ) * 𝐮) :=
    fmono hq (by rw [hu]; norm_num)
  have hqm : |z * eval R0 z / eval S0 z| ≤ (56723 / 1000000 : ℝ) := by
    rw [abs_div]
    exact (div_le_div₀ (by norm_num) hrm (by norm_num) hSm).trans (by norm_num)
  have hm := fapprox_mul hz hq' (4 : ℝ) (56723 / 1000000 : ℝ) hzm hqm _ le_rfl (by rw [hu]; norm_num)
  have hm' : FApprox (xa * xa * (xa * xa * hornerF (r0w.map Float.ofBits) (xa * xa) /
      hornerF (1.0 :: s0w.map Float.ofBits) (xa * xa))) (z * (z * eval R0 z / eval S0 z)) ((841 / 500 : ℝ) * 𝐮) :=
    fmono hm (by rw [hu]; norm_num)
  have hmm : |z * (z * eval R0 z / eval S0 z)| ≤ (56723 / 250000 : ℝ) := by
    rw [abs_mul]; exact (mul_le_mul hzm hqm (abs_nonneg _) (by norm_num)).trans (by norm_num)
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
  have hp := fapprox_mul hp1' hm1 (2 : ℝ) (1 / 16 : ℝ) (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [abs_of_nonneg (by linarith)]; linarith) _ le_rfl (by rw [hu]; norm_num)
  have hp' : FApprox ((1.0 + xa / 2.0) * (1.0 - xa / 2.0)) ((1 + v / 2) * (1 - v / 2)) ((47 / 250 : ℝ) * 𝐮) :=
    fmono hp (by rw [hu]; norm_num)
  have hpm : |(1 + v / 2) * (1 - v / 2)| ≤ (31 / 256 : ℝ) := by
    rw [abs_of_nonneg (by nlinarith)]; nlinarith
  have hres := fapprox_add_half hp' hm' 1020 (by norm_num) (by
    have e : (2 : ℝ) ^ (53 + 1020) / 2 ^ 1074 = (1 / 2 : ℝ) := by norm_num
    rw [e]
    have h1 := abs_add_le ((1 + v / 2) * (1 - v / 2)) (z * (z * eval R0 z / eval S0 z))
    have h2 : (47 / 250 : ℝ) * 𝐮 + (841 / 500 : ℝ) * 𝐮 < (1 / 2 : ℝ) - ((31 / 256 : ℝ) + (56723 / 250000 : ℝ)) := by rw [hu]; norm_num
    linarith)
  refine fmono (fcongr hres ?_) (by rw [hu]; norm_num)
  have : eval S0 z ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hSm; norm_num at hSm
  field_simp
  ring

#print axioms form2_0
#print axioms form2_1
#print axioms form2_2
#print axioms form2_3
#print axioms form2_4
end Library.Numerics.Float64.Bessel.BesselSmallJ0Form2
