import Verified.Examples.BesselMillerFacts
import Verified.Examples.BesselStepF

/-!
One step `b ⊗ dᵢ ⊘ x ⊖ a` of the backward recurrence of `jn`, in the form that keeps relative
errors bounded.  With `T = b J_(i-1)/J_i` the value that the step would give from an exact ratio,
`d ≥ J_(i+1)/J_(i-1)`, and `E` the relative error of the ratio `b/a` against `J_i/J_(i+1)`, the
result lies within `((1 + d) 2.03 u + d E (1 + 2E) + 1.01 u) T` of `T` (`bstep`).  The two
roundings of `b dᵢ/x` give `2 u` relative to `b λᵢ ≤ (1 + d) T`, the error of the ratio enters as
`(b J_(i+1) - a J_i)/J_i`, at most `d E (1 + 2E) T`, and the subtraction rounds once.
-/

namespace Verified.Examples.BesselMillerStep
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselStepF

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

set_option maxHeartbeats 1000000 in
/-- One step of the backward recurrence. -/
theorem bstep {a b di x : Float} {w Av Bv L J Jm Jp d E : ℝ} (i : ℕ)
    (ha : Finite a.toBits) (hb : Finite b.toBits) (hdi : FApprox di (2 * i) 0) (hx : FApprox x w 0)
    (hw : 1 / 2 ^ 30 ≤ w) (hw2 : w < 2) (hi : 1 ≤ i) (hi2 : i ≤ 2 ^ 31)
    (hAv : value a.toBits = Av) (hBv : value b.toBits = Bv) (hA0 : 0 < Av) (hB0 : 1 / 2 ^ 100 ≤ Bv)
    (hBm : Bv * L ≤ 2 ^ 1020)
    (hL : L = 2 * i / w) (hJ : 0 < J) (hJm : 0 < Jm) (hJp : 0 < Jp) (hrec : L * J = Jm + Jp)
    (hd : Jp ≤ d * Jm) (hd0 : 0 ≤ d) (hd2 : d ≤ 5)
    (hE : |Bv * Jp - Av * J| ≤ E * (Av * J)) (hE0 : 0 ≤ E) (hE1 : E ≤ 1 / 2 ^ 30) :
    Finite (b * di / x - a).toBits ∧
      |value (b * di / x - a).toBits - Bv * Jm / J| ≤
        ((1 + d) * (203 / 100) * 𝐮 + d * E * (1 + 2 * E) + 101 / 100 * 𝐮) * (Bv * Jm / J) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hir : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hB : 0 < Bv := lt_of_lt_of_le (by positivity) hB0
  -- the exact quantities
  set T := Bv * Jm / J with hT
  have hT0 : 0 < T := by positivity
  have hL1 : 1 ≤ L := by rw [hL, le_div_iff₀ hw0]; linarith
  have hBL : Bv * L = T + Bv * Jp / J := by
    rw [hT, ← add_div, ← mul_add, ← hrec]; field_simp
  have hBJp : Bv * Jp / J ≤ d * T := by
    rw [hT, div_le_iff₀ hJ]
    have : Bv * Jp ≤ Bv * (d * Jm) := mul_le_mul_of_nonneg_left hd hB.le
    have e : d * (Bv * Jm / J) * J = Bv * (d * Jm) := by field_simp
    linarith
  have hBJp0 : 0 ≤ Bv * Jp / J := by positivity
  -- `T ≥ Bv/3`, so the absolute terms are negligible
  have hTlow : Bv / 6 ≤ T := by
    have hJm2 : L * J ≤ (1 + d) * Jm := by nlinarith
    have hJ6 : J ≤ 6 * Jm := by nlinarith
    rw [hT, le_div_iff₀ hJ]
    nlinarith [mul_le_mul_of_nonneg_left hJ6 hB.le]
  -- `a` against `b J_(i+1)/J_i`
  have hAvb : |Bv * Jp / J - Av| ≤ E * Av := by
    rw [show Bv * Jp / J - Av = (Bv * Jp - Av * J) / J by field_simp, abs_div, abs_of_pos hJ,
      div_le_iff₀ hJ]
    linarith
  have hAv1 : Av ≤ (1 + 2 * E) * (d * T) := by
    have h1 := (abs_le.mp hAvb).1
    have h2 : Av * (1 - E) ≤ Bv * Jp / J := by linarith
    have h3 : Av ≤ (1 + 2 * E) * (Bv * Jp / J) := by
      have : (1 + 2 * E) * (1 - E) ≥ 1 := by nlinarith
      nlinarith
    have : (1 + 2 * E) * (Bv * Jp / J) ≤ (1 + 2 * E) * (d * T) :=
      mul_le_mul_of_nonneg_left hBJp (by linarith)
    linarith
  -- the three roundings
  have hbe : FApprox b Bv 0 := by rw [← hBv]; exact fapprox_exact b hb
  have hae : FApprox a Av 0 := by rw [← hAv]; exact fapprox_exact a ha
  have h2i : (0 : ℝ) ≤ 2 * i := by positivity
  have hp1 := fapprox_mul hbe hdi Bv (2 * i) (by rw [abs_of_pos hB]) (by rw [abs_of_nonneg h2i])
    (Bv * (2 * i)) (by simp) (by
      have e : Bv * (2 * i) = Bv * L * w := by rw [hL]; field_simp
      rw [e]
      have : Bv * L * w ≤ 2 ^ 1020 * 2 := by
        have h0 : 0 ≤ Bv * L := by
          have : 0 ≤ L := by rw [hL]; positivity
          positivity
        nlinarith
      linarith [show (2 : ℝ) ^ 1020 * 2 < 2 ^ 1022 by norm_num])
  have hp1' : FApprox (b * di) (Bv * (2 * i)) (Bv * (2 * i) / 2 ^ 53 + 1 / 2 ^ 1075) :=
    fmono hp1 (by simp)
  have hBi0 : 0 ≤ Bv * (2 * i) := by positivity
  have hp2 := fapprox_div hp1' hx (Bv * (2 * i)) w (by rw [abs_of_nonneg hBi0]) (le_abs_self w)
    (by linarith) (Bv * L * (1 + 1 / 2 ^ 50)) (by
      rw [sub_zero]
      have hLw : Bv * L * (1 + 1 / 2 ^ 50) = Bv * (2 * i) * (1 + 1 / 2 ^ 50) / w := by
        rw [hL]; ring
      rw [hLw]
      apply div_le_div_of_nonneg_right _ hw0.le
      have : (1 : ℝ) / 2 ^ 1075 ≤ Bv * (2 * i) / 2 ^ 60 := by
        rw [le_div_iff₀ (by positivity)]
        have : (2 : ℝ) ≤ 2 * i := by linarith
        nlinarith
      nlinarith) (by
      nlinarith [show (2 : ℝ) ^ 1020 * (1 + 1 / 2 ^ 50) < 2 ^ 1022 by norm_num])
  have hval2 : Bv * (2 * i) / w = Bv * L := by rw [hL]; ring
  rw [hval2] at hp2
  set e2 := (Bv * (2 * i) / 2 ^ 53 + 1 / 2 ^ 1075 + Bv * (2 * i) * 0 / w) / (w - 0) +
    Bv * L * (1 + 1 / 2 ^ 50) / 2 ^ 53 + 1 / 2 ^ 1075 with he2
  have he2b : e2 ≤ Bv * L * (2 * 𝐮 + 1 / 2 ^ 90) := by
    rw [he2, hu]
    have e : (Bv * (2 * i) / 2 ^ 53 + 1 / 2 ^ 1075 + Bv * (2 * i) * 0 / w) / (w - 0) =
        Bv * L / 2 ^ 53 + 1 / 2 ^ 1075 / w := by
      rw [hL]
      simp only [mul_zero, zero_div, add_zero, sub_zero]
      field_simp
    rw [e]
    have h1 : (1 : ℝ) / 2 ^ 1075 / w ≤ 2 ^ 30 / 2 ^ 1075 := by
      rw [div_le_iff₀ hw0]
      have : (2 : ℝ) ^ 30 / 2 ^ 1075 * w ≥ 2 ^ 30 / 2 ^ 1075 * (1 / 2 ^ 30) :=
        mul_le_mul_of_nonneg_left hw (by positivity)
      have e3 : (2 : ℝ) ^ 30 / 2 ^ 1075 * (1 / 2 ^ 30) = 1 / 2 ^ 1075 := by norm_num
      linarith
    have hBLlow : Bv / 3 ≤ Bv * L := by nlinarith
    have h2 : (2 : ℝ) ^ 30 / 2 ^ 1075 + 1 / 2 ^ 1075 ≤ Bv * L * (1 / 2 ^ 100) := by
      have : (2 : ℝ) ^ 30 / 2 ^ 1075 + 1 / 2 ^ 1075 ≤ 1 / 2 ^ 100 * (1 / 2 ^ 100 / 3) := by norm_num
      nlinarith
    nlinarith
  have hsub := fapprox_sub hp2 hae (|Bv * L - Av| + (e2 + 0)) le_rfl (by
    have hTBL : T ≤ Bv * L := by rw [hBL]; linarith
    have hAv6 : Av ≤ 6 * (Bv * L) := by
      have h1 : (1 + 2 * E) * (d * T) ≤ 6 * T := by
        have : 1 + 2 * E ≤ 6 / 5 := by linarith [show (2 : ℝ) * (1 / 2 ^ 30) ≤ 1 / 5 by norm_num]
        have : d * T ≤ 5 * T := mul_le_mul_of_nonneg_right hd2 hT0.le
        nlinarith
      linarith
    have h0 : 0 ≤ Bv * L := by linarith
    have : |Bv * L - Av| ≤ 6 * (Bv * L) := by
      rw [abs_le]; constructor <;> linarith
    have : e2 ≤ Bv * L := by
      have : 2 * 𝐮 + 1 / 2 ^ 90 ≤ 1 := by rw [hu]; norm_num
      nlinarith
    nlinarith [show (2 : ℝ) ^ 1020 * 7 < 2 ^ 1023 by norm_num])
  refine ⟨hsub.1, ?_⟩
  -- assemble
  have hd1 : |value (b * di / x - a).toBits - (Bv * L - Av)| ≤ e2 + 0 + (|Bv * L - Av| + (e2 + 0)) / 2 ^ 53 :=
    hsub.2
  have hgap : |Bv * L - Av - T| ≤ E * Av := by
    rw [show Bv * L - Av - T = Bv * Jp / J - Av by rw [hBL]; ring]; exact hAvb
  have hBLT : Bv * L ≤ (1 + d) * T := by rw [hBL]; nlinarith
  have hmid : |Bv * L - Av| ≤ T * (1 + 1 / 2 ^ 25) := by
    have : E * Av ≤ 1 / 2 ^ 25 * T := by
      have h1 : E * Av ≤ 1 / 2 ^ 30 * ((1 + 2 * E) * (d * T)) :=
        mul_le_mul hE1 hAv1 hA0.le (by norm_num)
      have h2 : (1 + 2 * E) * (d * T) ≤ 3 * 5 * T := by
        have : 1 + 2 * E ≤ 3 := by linarith [show (2 : ℝ) * (1 / 2 ^ 30) ≤ 2 by norm_num]
        nlinarith
      nlinarith
    rw [abs_le]; constructor <;> linarith [(abs_le.mp hgap).1, (abs_le.mp hgap).2]
  have htri := abs_sub_le (value (b * di / x - a).toBits) (Bv * L - Av) T
  rw [show Bv * L - Av - T = Bv * L - Av - T from rfl] at htri
  have hEA : E * Av ≤ d * E * (1 + 2 * E) * T := by
    have := mul_le_mul_of_nonneg_left hAv1 hE0
    linarith
  have he2T : e2 ≤ (1 + d) * T * (2 * 𝐮 + 1 / 2 ^ 90) := by
    have := mul_le_mul_of_nonneg_right hBLT (show 0 ≤ 2 * 𝐮 + 1 / 2 ^ 90 by rw [hu]; positivity)
    linarith
  rw [hu] at he2T ⊢
  have hfin : e2 + 0 + (|Bv * L - Av| + (e2 + 0)) / 2 ^ 53 ≤
      (1 + d) * T * (2 * (1 / 2 ^ 53) + 1 / 2 ^ 90) * (1 + 1 / 2 ^ 53) + T * (1 + 1 / 2 ^ 25) / 2 ^ 53 := by
    have : 0 ≤ e2 := le_trans (abs_nonneg _) hp2.2
    nlinarith
  have hslack : (1 + d) * T * (2 * (1 / 2 ^ 53) + 1 / 2 ^ 90) * (1 + 1 / 2 ^ 53) +
      T * (1 + 1 / 2 ^ 25) / 2 ^ 53 ≤ ((1 + d) * (203 / 100) * (1 / 2 ^ 53) + 101 / 100 * (1 / 2 ^ 53)) * T := by
    have h1 : ((2 : ℝ) * (1 / 2 ^ 53) + 1 / 2 ^ 90) * (1 + 1 / 2 ^ 53) ≤ 203 / 100 * (1 / 2 ^ 53) := by
      norm_num
    have h2 : (1 + 1 / 2 ^ 25 : ℝ) / 2 ^ 53 ≤ 101 / 100 * (1 / 2 ^ 53) := by norm_num
    have h3 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ (1 + d) * T by positivity)
    have h4 := mul_le_mul_of_nonneg_left h2 hT0.le
    nlinarith
  nlinarith

#print axioms bstep

end Verified.Examples.BesselMillerStep
