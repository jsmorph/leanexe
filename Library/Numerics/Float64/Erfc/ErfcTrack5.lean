import Library.Numerics.Float64.Erfc.ErfcTrack4
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
The stages of `erfc_asympt_accurate` in the form of `ErfcTrack`.  `pr_twoSum` adds a float to a
double-double by Knuth's `two_sum`, exact without a condition on the order of the operands, and
`pr_twoSumB` adds a double-double coefficient.  `pr_renorm` is the `fast_two_sum` that renormalizes
a double-double, and `tStep` and `tStepB` are the loop steps of the polynomial of `Tacc`:
`Erfc.dMul` by `(uh, ul)` followed by `pr_twoSum` or `pr_twoSumB` (`pr_tStep`, `pr_tStepB`).
-/

namespace Library.Numerics.Float64.Erfc.ErfcTrack5

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack4 Library.Numerics.Arithmetic.Fma.FmaSpec

set_option exponentiation.threshold 2200

local notation "u" => (1 / 2 ^ 53 : ℝ)
local notation "η" => (1 / 2 ^ 1075 : ℝ)

theorem twoSum_fst (a b : Float) : (Erfc.twoSum a b).1 = a + b := rfl

/-- `c + (h, l)` by `two_sum (c, h)` with `l` added to its error term. -/
theorem pr_twoSum {c h l : Float} {V M L e Mc : ℝ} (hc : ff c) (hMc : |fv c| ≤ Mc)
    (hp : Pr h l V M L e) (H M' L' e' T : ℝ) (hH : M + e + L ≤ H) (hT : u * (Mc + H) + η ≤ T)
    (hM : Mc + M ≤ M') (hL : (T + L) * (1 + u) ≤ L') (he : e + u * (T + L) ≤ e')
    (hov : Mc + H + L + T ≤ 2 ^ 1000) :
    Pr (Erfc.twoSum c h).1 ((Erfc.twoSum c h).2 + l) (fv c + V) M' L' e' := by
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hL0 := hp.L_nonneg
  have he0 := hp.e_nonneg
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hMc0 : 0 ≤ Mc := (abs_nonneg _).trans hMc
  have k : (2 : ℝ) ^ 1000 ≤ 2 ^ 1018 := by norm_num
  obtain ⟨f1, f2, fsum, -, -⟩ := twoSum_f c h hc hp.1 (hMc.trans (by linarith))
    (hhH.trans (by linarith))
  have hs : |fv c + fv h| ≤ Mc + H := (abs_add_le _ _).trans (by linarith)
  have k18 : (2 : ℝ) ^ 1018 ≤ 2 ^ 1022 := by norm_num
  obtain ⟨-, serr⟩ := add_f c h hc hp.1 (hs.trans (by linarith))
  rw [← twoSum_fst] at serr
  have hT' : |fv (Erfc.twoSum c h).2| ≤ T := by
    have e1 : fv (Erfc.twoSum c h).2 = -(fv (Erfc.twoSum c h).1 - (fv c + fv h)) := by linarith
    rw [e1, abs_neg]
    refine serr.trans ?_
    have : u * |fv c + fv h| ≤ u * (Mc + H) := by gcongr
    linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT'
  obtain ⟨s1, serr2, smag⟩ := add_bound f2 hp.2.1 hT' hp.2.2.2.2 (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · have e1 : fv (Erfc.twoSum c h).1 + fv ((Erfc.twoSum c h).2 + l) - (fv c + V) =
        (fv h + fv l - V) +
          (fv ((Erfc.twoSum c h).2 + l) - (fv (Erfc.twoSum c h).2 + fv l)) := by linarith
    rw [e1]
    exact (abs_add_le _ _).trans (by linarith [hp.2.2.1])
  · exact (abs_add_le _ _).trans (by linarith [hp.2.2.2.1])

/-- `(c + d) + (h, l)` by `two_sum (c, h)` with `l + d` added to its error term. -/
theorem pr_twoSumB {c d h l : Float} {V M L e Mc Md : ℝ} (hc : ff c) (hMc : |fv c| ≤ Mc)
    (hd : ff d) (hMd : |fv d| ≤ Md) (hp : Pr h l V M L e)
    (H M' L' e' T Vb : ℝ) (hH : M + e + L ≤ H) (hT : u * (Mc + H) + η ≤ T)
    (hVb : (L + Md) * (1 + u) ≤ Vb) (hM : Mc + Md + M ≤ M') (hL : (T + Vb) * (1 + u) ≤ L')
    (he : e + u * (L + Md) + u * (T + Vb) ≤ e') (hov : Mc + H + L + Md + T + Vb ≤ 2 ^ 1000) :
    Pr (Erfc.twoSum c h).1 ((Erfc.twoSum c h).2 + (l + d)) (fv c + fv d + V) M' L' e' := by
  have hhH : |fv h| ≤ H := hp.h_le.trans hH
  have hL0 := hp.L_nonneg
  have he0 := hp.e_nonneg
  have hH0 : 0 ≤ H := (abs_nonneg _).trans hhH
  have hMc0 : 0 ≤ Mc := (abs_nonneg _).trans hMc
  have hMd0 : 0 ≤ Md := (abs_nonneg _).trans hMd
  have k : (2 : ℝ) ^ 1000 ≤ 2 ^ 1018 := by norm_num
  obtain ⟨f1, f2, fsum, -, -⟩ := twoSum_f c h hc hp.1 (hMc.trans (by linarith))
    (hhH.trans (by linarith))
  have hs : |fv c + fv h| ≤ Mc + H := (abs_add_le _ _).trans (by linarith)
  have k18 : (2 : ℝ) ^ 1018 ≤ 2 ^ 1022 := by norm_num
  obtain ⟨-, serr⟩ := add_f c h hc hp.1 (hs.trans (by linarith))
  rw [← twoSum_fst] at serr
  have hT' : |fv (Erfc.twoSum c h).2| ≤ T := by
    have e1 : fv (Erfc.twoSum c h).2 = -(fv (Erfc.twoSum c h).1 - (fv c + fv h)) := by linarith
    rw [e1, abs_neg]
    refine serr.trans ?_
    have : u * |fv c + fv h| ≤ u * (Mc + H) := by gcongr
    linarith
  have hT0 : 0 ≤ T := (abs_nonneg _).trans hT'
  obtain ⟨v1, verr, vmag⟩ := add_bound hp.2.1 hd hp.2.2.2.2 hMd (by linarith)
  have hv : |fv (l + d)| ≤ Vb := vmag.trans hVb
  have hVb0 : 0 ≤ Vb := (abs_nonneg _).trans hv
  obtain ⟨s1, serr2, smag⟩ := add_bound f2 v1 hT' hv (by linarith)
  refine ⟨f1, s1, ?_, ?_, smag.trans hL⟩
  · have e1 : fv (Erfc.twoSum c h).1 + fv ((Erfc.twoSum c h).2 + (l + d)) -
        (fv c + fv d + V) = (fv h + fv l - V) + (fv (l + d) - (fv l + fv d)) +
          (fv ((Erfc.twoSum c h).2 + (l + d)) - (fv (Erfc.twoSum c h).2 + fv (l + d))) := by
      linarith
    rw [e1]
    exact (abs_add3 _ _ _).trans (by linarith [hp.2.2.1])
  · refine (abs_add_le _ _).trans ?_
    have := abs_add_le (fv c) (fv d)
    linarith [hp.2.2.2.1]

/-- The renormalization of a double-double by `fast_two_sum (h, l)`, exact for `|l| ≤ |h|`. -/
theorem pr_renorm {h l : Float} {V M L e : ℝ} (hp : Pr h l V M L e) (hlh : |fv l| ≤ |fv h|)
    (L' : ℝ) (hL : u * (M + e + L + L) ≤ L') (hov : M + e + L + L ≤ 2 ^ 1000) :
    Pr (Erfc.fastTwoSum h l).1 (Erfc.fastTwoSum h l).2 V M L' e := by
  have hhH := hp.h_le
  obtain ⟨f1, f2, fsum, ft⟩ := fts_bound hp.1 hp.2.1 hhH hp.2.2.2.2 hlh hov
  refine ⟨f1, f2, by rw [fsum]; exact hp.2.2.1, hp.2.2.2.1, ft.trans hL⟩

/-- The step of the first loop of `erfc_asympt_accurate`'s polynomial. -/
def tStep (uh ul c : Float) (s : Float × Float) : Float × Float :=
  let (h, l) := Erfc.aMul s.1 uh
  let l := Library.Numerics.Arithmetic.Fma.fma s.1 ul l
  let l := Library.Numerics.Arithmetic.Fma.fma s.2 uh l
  let (zh, zl) := Erfc.twoSum c h
  (zh, zl + l)

/-- The step of the second loop, with the double-double coefficient `c + d`. -/
def tStepB (uh ul c d : Float) (s : Float × Float) : Float × Float :=
  let (h, l) := Erfc.aMul s.1 uh
  let l := Library.Numerics.Arithmetic.Fma.fma s.1 ul l
  let l := Library.Numerics.Arithmetic.Fma.fma s.2 uh l
  let (zh, zl) := Erfc.twoSum c h
  (zh, zl + (l + d))

theorem tStep_eq (uh ul c : Float) (s : Float × Float) :
    tStep uh ul c s = ((Erfc.twoSum c (Erfc.dMul s.1 s.2 uh ul).1).1,
      (Erfc.twoSum c (Erfc.dMul s.1 s.2 uh ul).1).2 + (Erfc.dMul s.1 s.2 uh ul).2) := rfl

theorem tStepB_eq (uh ul c d : Float) (s : Float × Float) :
    tStepB uh ul c d s = ((Erfc.twoSum c (Erfc.dMul s.1 s.2 uh ul).1).1,
      (Erfc.twoSum c (Erfc.dMul s.1 s.2 uh ul).1).2 + ((Erfc.dMul s.1 s.2 uh ul).2 + d)) := rfl

/-- The bounds of one step of the first loop over a field: from the bounds `(M, L, e)` of the
state, the coefficient's magnitude `Mc`, and the bounds `MU`, `LU` of `U = uh + ul`, the bounds of
`Erfc.dMul` and of `two_sum` with the low parts added. -/
def stepF {K : Type} [Field K] (M L e Mc MU LU : K) : K × K × K :=
  let r : K := 1 / 2 ^ 53
  let t : K := 1 / 2 ^ 1075
  let HA := M + e + L
  let HB := MU + LU
  let Ttl := r * r * (HA * HB) + 2 * t + (r * (HA * HB) + t)
  let F1 := (HA * LU + Ttl) * (1 + r) + t
  let dL := (L * HB + F1) * (1 + r) + t
  let de := MU * e + L * LU + (r * r * (HA * HB) + 2 * t) + (r * (HA * LU + Ttl) + t) +
    (r * (L * HB + F1) + t)
  let T := r * (Mc + (M * MU + de + dL)) + t
  (Mc + M * MU, (T + dL) * (1 + r), de + r * (T + dL))

/-- The bounds of one step of the second loop, with the coefficient `c + d`, `|c| ≤ Mc`, `|d| ≤ Md`. -/
def stepFB {K : Type} [Field K] (M L e Mc Md MU LU : K) : K × K × K :=
  let r : K := 1 / 2 ^ 53
  let t : K := 1 / 2 ^ 1075
  let HA := M + e + L
  let HB := MU + LU
  let Ttl := r * r * (HA * HB) + 2 * t + (r * (HA * HB) + t)
  let F1 := (HA * LU + Ttl) * (1 + r) + t
  let dL := (L * HB + F1) * (1 + r) + t
  let de := MU * e + L * LU + (r * r * (HA * HB) + 2 * t) + (r * (HA * LU + Ttl) + t) +
    (r * (L * HB + F1) + t)
  let T := r * (Mc + (M * MU + de + dL)) + t
  let Vb := (dL + Md) * (1 + r)
  (Mc + Md + M * MU, (T + Vb) * (1 + r), de + r * (dL + Md) + r * (T + Vb))

/-- The overflow conditions of one step over `ℚ`. -/
def stepOK (M L e Mc Md MU LU : ℚ) : Prop :=
  0 ≤ M ∧ 0 ≤ L ∧ 0 ≤ e ∧ 0 ≤ Mc ∧ 0 ≤ Md ∧ 0 ≤ MU ∧ 0 ≤ LU ∧
    M + e + L ≤ 2 ^ 400 ∧ MU + LU ≤ 1 ∧ Mc + Md ≤ 2 ^ 400

instance (M L e Mc Md MU LU : ℚ) : Decidable (stepOK M L e Mc Md MU LU) := by
  unfold stepOK; infer_instance

theorem stepF_cast (M L e Mc MU LU : ℚ) :
    (((stepF M L e Mc MU LU).1 : ℚ) : ℝ) = (stepF (M : ℝ) L e Mc MU LU).1 ∧
      (((stepF M L e Mc MU LU).2.1 : ℚ) : ℝ) = (stepF (M : ℝ) L e Mc MU LU).2.1 ∧
      (((stepF M L e Mc MU LU).2.2 : ℚ) : ℝ) = (stepF (M : ℝ) L e Mc MU LU).2.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [stepF] <;> push_cast <;> ring

theorem stepFB_cast (M L e Mc Md MU LU : ℚ) :
    (((stepFB M L e Mc Md MU LU).1 : ℚ) : ℝ) = (stepFB (M : ℝ) L e Mc Md MU LU).1 ∧
      (((stepFB M L e Mc Md MU LU).2.1 : ℚ) : ℝ) = (stepFB (M : ℝ) L e Mc Md MU LU).2.1 ∧
      (((stepFB M L e Mc Md MU LU).2.2 : ℚ) : ℝ) = (stepFB (M : ℝ) L e Mc Md MU LU).2.2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [stepFB] <;> push_cast <;> ring

/-- The step of the first loop on a `Pr` of `V`, with `|c| ≤ Mc`. -/
theorem pr_tStep (hF : FmaNearest) {uh ul c : Float} {s : Float × Float} {U V : ℝ}
    {M L e Mc MU LU : ℝ} (hU : Pr uh ul U MU LU 0) (hs : Pr s.1 s.2 V M L e) (hc : ff c)
    (hMc : |fv c| ≤ Mc) (h0 : 0 ≤ Mc) (hMb : M + e + L ≤ 2 ^ 400) (hUb : MU + LU ≤ 1)
    (hcb : Mc ≤ 2 ^ 400) :
    Pr (tStep uh ul c s).1 (tStep uh ul c s).2 (fv c + V * U) (stepF M L e Mc MU LU).1
      (stepF M L e Mc MU LU).2.1 (stepF M L e Mc MU LU).2.2 := by
  have hM0 := hs.M_nonneg
  have hL0 := hs.L_nonneg
  have he0 := hs.e_nonneg
  have hMU0 := hU.M_nonneg
  have hLU0 := hU.L_nonneg
  have hu : (0 : ℝ) ≤ u := by norm_num
  have hη : (0 : ℝ) ≤ η := by norm_num
  have hHAB : (M + e + L) * (MU + LU) ≤ 2 ^ 400 := by nlinarith
  have hd := pr_dMul hF hs hU (M + e + L) (MU + LU)
    (u * u * ((M + e + L) * (MU + LU)) + 2 * η + (u * ((M + e + L) * (MU + LU)) + η))
    (((M + e + L) * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η +
      (u * ((M + e + L) * (MU + LU)) + η))) * (1 + u) + η)
    (M * MU)
    ((L * (MU + LU) + (((M + e + L) * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η +
      (u * ((M + e + L) * (MU + LU)) + η))) * (1 + u) + η)) * (1 + u) + η)
    (MU * e + L * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η) +
      (u * ((M + e + L) * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η +
        (u * ((M + e + L) * (MU + LU)) + η))) + η) +
      (u * (L * (MU + LU) + (((M + e + L) * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η +
        (u * ((M + e + L) * (MU + LU)) + η))) * (1 + u) + η)) + η))
    le_rfl (by linarith) le_rfl le_rfl le_rfl le_rfl (by nlinarith) (by
      have : (M + e + L) * LU ≤ 2 ^ 400 := by nlinarith
      have : L * (MU + LU) ≤ 2 ^ 400 := by nlinarith
      nlinarith)
  rw [tStep_eq]
  refine (pr_twoSum hc hMc hd _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl le_rfl ?_).mono ?_ ?_ ?_
  · have : (M + e + L) * LU ≤ 2 ^ 400 := by nlinarith
    have : L * (MU + LU) ≤ 2 ^ 400 := by nlinarith
    have : M * MU ≤ 2 ^ 400 := by nlinarith
    nlinarith
  all_goals (simp only [stepF] <;> linarith)

/-- The step of the second loop on a `Pr` of `V`, with `|c| ≤ Mc` and `|d| ≤ Md`. -/
theorem pr_tStepB (hF : FmaNearest) {uh ul c d : Float} {s : Float × Float} {U V : ℝ}
    {M L e Mc Md MU LU : ℝ} (hU : Pr uh ul U MU LU 0) (hs : Pr s.1 s.2 V M L e) (hc : ff c)
    (hMc : |fv c| ≤ Mc) (hd : ff d) (hMd : |fv d| ≤ Md) (h0 : 0 ≤ Mc) (h0' : 0 ≤ Md)
    (hMb : M + e + L ≤ 2 ^ 400) (hUb : MU + LU ≤ 1) (hcb : Mc + Md ≤ 2 ^ 400) :
    Pr (tStepB uh ul c d s).1 (tStepB uh ul c d s).2 (fv c + fv d + V * U)
      (stepFB M L e Mc Md MU LU).1 (stepFB M L e Mc Md MU LU).2.1
      (stepFB M L e Mc Md MU LU).2.2 := by
  have hM0 := hs.M_nonneg
  have hL0 := hs.L_nonneg
  have he0 := hs.e_nonneg
  have hMU0 := hU.M_nonneg
  have hLU0 := hU.L_nonneg
  have hu : (0 : ℝ) ≤ u := by norm_num
  have hη : (0 : ℝ) ≤ η := by norm_num
  have hHAB : (M + e + L) * (MU + LU) ≤ 2 ^ 400 := by nlinarith
  have hd' := pr_dMul hF hs hU (M + e + L) (MU + LU)
    (u * u * ((M + e + L) * (MU + LU)) + 2 * η + (u * ((M + e + L) * (MU + LU)) + η))
    (((M + e + L) * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η +
      (u * ((M + e + L) * (MU + LU)) + η))) * (1 + u) + η)
    (M * MU)
    ((L * (MU + LU) + (((M + e + L) * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η +
      (u * ((M + e + L) * (MU + LU)) + η))) * (1 + u) + η)) * (1 + u) + η)
    (MU * e + L * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η) +
      (u * ((M + e + L) * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η +
        (u * ((M + e + L) * (MU + LU)) + η))) + η) +
      (u * (L * (MU + LU) + (((M + e + L) * LU + (u * u * ((M + e + L) * (MU + LU)) + 2 * η +
        (u * ((M + e + L) * (MU + LU)) + η))) * (1 + u) + η)) + η))
    le_rfl (by linarith) le_rfl le_rfl le_rfl le_rfl (by nlinarith) (by
      have : (M + e + L) * LU ≤ 2 ^ 400 := by nlinarith
      have : L * (MU + LU) ≤ 2 ^ 400 := by nlinarith
      nlinarith)
  rw [tStepB_eq]
  refine (pr_twoSumB hc hMc hd hMd hd' _ _ _ _ _ _ le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    ?_).mono ?_ ?_ ?_
  · have : (M + e + L) * LU ≤ 2 ^ 400 := by nlinarith
    have : L * (MU + LU) ≤ 2 ^ 400 := by nlinarith
    have : M * MU ≤ 2 ^ 400 := by nlinarith
    nlinarith
  all_goals (simp only [stepFB] <;> linarith)

#print axioms pr_twoSum
#print axioms pr_twoSumB
#print axioms pr_renorm
#print axioms pr_tStep
#print axioms pr_tStepB
#print axioms stepF_cast

end Library.Numerics.Float64.Erfc.ErfcTrack5
