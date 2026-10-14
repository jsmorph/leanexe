import Verified.Examples.ErfcTrack4
import Verified.Examples.ErfcFastMain
import Verified.Examples.ErfcRound
import Verified.Examples.ErfcCast

/-!
`q_1` of `Erfc`: `exp z` for the double-double `z = zh + zl` with `|z| < 0.000130273`, as
`1 + z (1 + z (1/2 + z (c3 + c4 zh)))`.  `q1Core` takes the constants as arguments, and `q1_pr`
bounds the distance of the computed double-double from that polynomial when `Q1Hyp` holds;
`q1_exp` adds the distance of the polynomial from `exp z`, from Taylor's bound
(`Real.exp_bound`) and the distances of `c3` and `c4` from `1/6` and `1/24`.
-/

namespace Verified.Examples.ErfcQ1

open CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcTrack ErfcTrack2 ErfcTrack4 ErfcFastMain ErfcRound
  FmaSpec PolyBound

set_option exponentiation.threshold 2200

/-- `Erfc.q1` with its constants as arguments. -/
def q1Core (c4 c3 half one zh zl : Float) : Float × Float :=
  let z := zh + zl
  let q := Fma.fma c4 zh c3
  let q := Fma.fma q z half
  let (hi, lo) := Erfc.fastTwoSum one (q * z)
  let (hi, lo) := Erfc.dMul zh zl hi lo
  Erfc.fastSum one hi lo

theorem q1_eq (zh zl : Float) :
    Erfc.q1 zh zl = q1Core (Float.ofBits 0x3FA55555558489DC) (Float.ofBits 0x3FC5555555995D37)
      0.5 1.0 zh zl := rfl

/-- `c3` and `c4`. -/
def q1Q : List ℚ := [ratOfWord 0x3FC5555555995D37, ratOfWord 0x3FA55555558489DC]

/-- The bounds of the stages, as `q1B` computes them. -/
structure Q1B where
  (zM ze a1M a1e a2M a2e pM pe : ℚ)
  (fM fL fe dHA dHB dTtl dF1 dM : ℚ)
  (dL de sH sT sM sL se : ℚ)

set_option maxHeartbeats 4000000 in
/-- The bounds of the stages. -/
def q1B (q : List ℚ) (R Rh Lz : ℚ) : Q1B :=
  let zM := Rh + Lz
  let ze := 0 + 0 + (1 / 2 ^ 53) * (zM + 0 + 0)
  let a1M := qabs (q.getD 1 0) * Rh + qabs (q.getD 0 0)
  let a1e := 0 * Rh + qabs (q.getD 1 0) * 0 + 0 * 0 + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 1 0) + 0) * (Rh + 0) + qabs (q.getD 0 0) + 0) + (1 / 2 ^ 1075)
  let a2M := a1M * zM + 1 / 2
  let a2e := a1e * zM + a1M * ze + a1e * ze + 0 + (1 / 2 ^ 53) * ((a1M + a1e) * (zM + ze) + 1 / 2 + 0) + (1 / 2 ^ 1075)
  let pM := a2M * zM
  let pe := a2e * zM + a2M * ze + a2e * ze + (1 / 2 ^ 53) * ((a2M + a2e) * (zM + ze)) + (1 / 2 ^ 1075)
  let fM := 1 + pM
  let fL := (1 / 2 ^ 53) * (fM + 0 + pe)
  let fe := 0 + pe
  let dHA := R + 0 + Lz
  let dHB := fM + fe + fL
  let dTtl := (1 / 2 ^ 53) * (1 / 2 ^ 53) * (dHA * dHB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (dHA * dHB) + (1 / 2 ^ 1075))
  let dF1 := (dHA * fL + dTtl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let dM := R * fM
  let dL := (Lz * dHB + dF1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075)
  let de := (R + 0) * fe + fM * 0 + Lz * fL + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (dHA * dHB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (dHA * fL + dTtl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (Lz * dHB + dF1) + (1 / 2 ^ 1075))
  let sH := dM + de + dL
  let sT := (1 / 2 ^ 53) * (1 + sH)
  let sM := 1 + dM
  let sL := (sT + dL) * (1 + (1 / 2 ^ 53))
  let se := de + (1 / 2 ^ 53) * (sT + dL)
  ⟨zM, ze, a1M, a1e, a2M, a2e, pM, pe, fM, fL, fe, dHA, dHB, dTtl, dF1, dM, dL, de, sH, sT, sM, sL, se⟩

set_option maxHeartbeats 4000000 in
/-- The conditions on the bounds `b`: each bound at least its formula, and the dominance
and overflow conditions of the stages. -/
def Q1Hyp (q : List ℚ) (R Rh Lz : ℚ) (b : Q1B) : Prop :=
  Rh + Lz ≤ b.zM ∧
  0 + 0 + (1 / 2 ^ 53) * (b.zM + 0 + 0) ≤ b.ze ∧
  qabs (q.getD 1 0) * Rh + qabs (q.getD 0 0) ≤ b.a1M ∧
  0 * Rh + qabs (q.getD 1 0) * 0 + 0 * 0 + 0 + (1 / 2 ^ 53) * ((qabs (q.getD 1 0) + 0) * (Rh + 0) + qabs (q.getD 0 0) + 0) + (1 / 2 ^ 1075) ≤ b.a1e ∧
  b.a1M * b.zM + 1 / 2 ≤ b.a2M ∧
  b.a1e * b.zM + b.a1M * b.ze + b.a1e * b.ze + 0 + (1 / 2 ^ 53) * ((b.a1M + b.a1e) * (b.zM + b.ze) + 1 / 2 + 0) + (1 / 2 ^ 1075) ≤ b.a2e ∧
  b.a2M * b.zM ≤ b.pM ∧
  b.a2e * b.zM + b.a2M * b.ze + b.a2e * b.ze + (1 / 2 ^ 53) * ((b.a2M + b.a2e) * (b.zM + b.ze)) + (1 / 2 ^ 1075) ≤ b.pe ∧
  1 + b.pM ≤ b.fM ∧
  (1 / 2 ^ 53) * (b.fM + 0 + b.pe) ≤ b.fL ∧
  0 + b.pe ≤ b.fe ∧
  R + 0 + Lz ≤ b.dHA ∧
  b.fM + b.fe + b.fL ≤ b.dHB ∧
  (1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.dHA * b.dHB) + 2 * (1 / 2 ^ 1075) + ((1 / 2 ^ 53) * (b.dHA * b.dHB) + (1 / 2 ^ 1075)) ≤ b.dTtl ∧
  (b.dHA * b.fL + b.dTtl) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.dF1 ∧
  R * b.fM ≤ b.dM ∧
  (Lz * b.dHB + b.dF1) * (1 + (1 / 2 ^ 53)) + (1 / 2 ^ 1075) ≤ b.dL ∧
  (R + 0) * b.fe + b.fM * 0 + Lz * b.fL + ((1 / 2 ^ 53) * (1 / 2 ^ 53) * (b.dHA * b.dHB) + 2 * (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (b.dHA * b.fL + b.dTtl) + (1 / 2 ^ 1075)) + ((1 / 2 ^ 53) * (Lz * b.dHB + b.dF1) + (1 / 2 ^ 1075)) ≤ b.de ∧
  b.dM + b.de + b.dL ≤ b.sH ∧
  (1 / 2 ^ 53) * (1 + b.sH) ≤ b.sT ∧
  1 + b.dM ≤ b.sM ∧
  (b.sT + b.dL) * (1 + (1 / 2 ^ 53)) ≤ b.sL ∧
  b.de + (1 / 2 ^ 53) * (b.sT + b.dL) ≤ b.se ∧
  b.zM + 0 + 0 ≤ 2 ^ 1000 ∧
  (qabs (q.getD 1 0) + 0) * (Rh + 0) + qabs (q.getD 0 0) + 0 ≤ 2 ^ 1000 ∧
  (b.a1M + b.a1e) * (b.zM + b.ze) + 1 / 2 + 0 ≤ 2 ^ 1000 ∧
  (b.a2M + b.a2e) * (b.zM + b.ze) ≤ 2 ^ 1000 ∧
  b.pM + b.pe + 0 ≤ 1 ∧
  b.fM + 0 + b.pe ≤ 2 ^ 1000 ∧
  b.dHA * b.dHB + b.dHA * b.fL + Lz * b.dHB + b.dTtl + b.dF1 ≤ 2 ^ 1000 ∧
  b.sH ≤ 1 ∧
  1 + b.sH + b.dL + b.sT ≤ 2 ^ 1000

set_option synthInstance.maxSize 4096 in
instance (q : List ℚ) (R Rh Lz : ℚ) (b : Q1B) : Decidable (Q1Hyp q R Rh Lz b) := by
  unfold Q1Hyp; infer_instance

set_option maxHeartbeats 4000000 in
theorem q1_core_pr (hF : FmaNearest) (c4 c3 half one zh zl : Float) (hzh : ff zh) (hzl : ff zl)
    (R Rh Lz : ℚ) (hZ : |fv zh + fv zl| ≤ R) (hRh : |fv zh| ≤ Rh) (hLz : |fv zl| ≤ Lz) (b : Q1B)
    (hb : Q1Hyp q1Q R Rh Lz b) (k3 : ff c3 ∧ fv c3 = q1Q.getD 0 0)
    (k4 : ff c4 ∧ fv c4 = q1Q.getD 1 0) (kh : ff half ∧ fv half = 1 / 2)
    (k1 : ff one ∧ fv one = 1) :
    Pr (q1Core c4 c3 half one zh zl).1 (q1Core c4 c3 half one zh zl).2
      (fv one + (fv zh + fv zl) *
        (fv one + ((fv c4 * fv zh + fv c3) * (fv zh + fv zl) + fv half) * (fv zh + fv zl)))
      b.sM b.sL b.se := by
  obtain ⟨f_zM, f_ze, f_a1M, f_a1e, f_a2M, f_a2e, f_pM, f_pe, f_fM, f_fL, f_fe, f_dHA, f_dHB,
    f_dTtl, f_dF1, f_dM, f_dL, f_de, f_sH, f_sT, f_sM, f_sL, f_se, h_zov, h_a1ov, h_a2ov, h_pov,
    h_fpre, h_fov, h_dov, h_spre, h_sov⟩ := hb
  have t3 := coef_tr _ _ k3
  have t4 := coef_tr _ _ k4
  have tzh : Tr zh (fv zh) Rh 0 := tr_exact zh hzh Rh hRh
  have tzl : Tr zl (fv zl) Lz 0 := tr_exact zl hzl Lz hLz
  have thalf : Tr half (fv half) (1 / 2) 0 :=
    tr_exact half kh.1 _ (by rw [kh.2]; norm_num)
  have tone : Tr one (fv one) 1 0 := tr_exact one k1.1 _ (by rw [k1.2]; norm_num)
  have r_z := tr_add tzh tzl b.zM b.ze (by qcast f_zM) (by qcast f_ze) (by qcast h_zov)
  have r_a1 := tr_fma hF t4 tzh t3 b.a1M b.a1e (by qcast f_a1M) (by qcast f_a1e) (by qcast h_a1ov)
  have r_a2 := tr_fma hF r_a1 r_z thalf b.a2M b.a2e (by qcast f_a2M) (by qcast f_a2e)
    (by qcast h_a2ov)
  have r_p := tr_mul r_a2 r_z b.pM b.pe (by qcast f_pM) (by qcast f_pe) (by qcast h_pov)
  have s_f := (pr_fts tone r_p 1 (show (1 : ℝ) ≤ |fv one| by rw [k1.2, abs_one]) (by qcast h_fpre) b.fM b.fL
    (by qcast f_fM) (by qcast f_fL) (by qcast h_fov)).mono (M' := b.fM) (L' := b.fL)
    (e' := b.fe) le_rfl le_rfl (by qcast f_fe)
  have pz : Pr zh zl (fv zh + fv zl) R Lz 0 :=
    ⟨hzh, hzl, by simp, by qc hZ, by qc hLz⟩
  have s_d := pr_dMul hF pz s_f b.dHA b.dHB b.dTtl b.dF1 b.dM b.dL b.de (by qcast f_dHA)
    (by qcast f_dHB) (by qcast f_dTtl) (by qcast f_dF1) (by qcast f_dM) (by qcast f_dL)
    (by qcast f_de) (by qcast h_dov)
  have s_s := pr_fastSum k1.1 (show |fv one| ≤ 1 by rw [k1.2, abs_one])
    (show (1 : ℝ) ≤ |fv one| by rw [k1.2, abs_one])
    s_d b.sH b.sM b.sL b.se b.sT (by qcast f_sH) (by qcast h_spre) (by qcast f_sT)
    (by qcast f_sM) (by qcast f_sL) (by qcast f_se) (by qcast h_sov)
  unfold q1Core
  dsimp only
  exact s_s

/-- The polynomial of `q_1` against `exp`. -/
theorem q1_exp (zh zl c3 c4 : ℝ) (R Lz : ℝ) (hZ : |zh + zl| ≤ R) (hR1 : R ≤ 1) (hzl : |zl| ≤ Lz)
    (hc4 : 0 ≤ c4) :
    |Real.exp (zh + zl) - (1 + (zh + zl) * (1 + ((c4 * zh + c3) * (zh + zl) + 1 / 2) * (zh + zl)))| ≤
      R ^ 5 * (6 / 600) + R ^ 3 * (|1 / 6 - c3| + R * |1 / 24 - c4| + c4 * Lz) := by
  set Z := zh + zl with hZdef
  have hR0 : 0 ≤ R := (abs_nonneg _).trans hZ
  have ht := Real.exp_bound (x := Z) (hZ.trans hR1) (n := 5) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at ht
  norm_num at ht
  have e1 : Real.exp Z - (1 + Z * (1 + ((c4 * zh + c3) * Z + 1 / 2) * Z)) =
      (Real.exp Z - (1 + Z + Z ^ 2 / 2 + Z ^ 3 / 6 + Z ^ 4 / 24)) +
        Z ^ 3 * ((1 / 6 - c3) + Z * (1 / 24 - c4) + c4 * zl) := by
    rw [hZdef]; ring
  rw [e1]
  refine (abs_add_le _ _).trans ?_
  have hZ3 : |Z ^ 3| ≤ R ^ 3 := by rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hZ 3
  have hZ5 : |Z| ^ 5 ≤ R ^ 5 := pow_le_pow_left₀ (abs_nonneg _) hZ 5
  have hin : |(1 / 6 - c3) + Z * (1 / 24 - c4) + c4 * zl| ≤
      |1 / 6 - c3| + R * |1 / 24 - c4| + c4 * Lz := by
    refine (abs_add3 _ _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg hc4]
    have := mul_le_mul_of_nonneg_right hZ (abs_nonneg (1 / 24 - c4))
    have := mul_le_mul_of_nonneg_left hzl hc4
    linarith
  have k1 : |Z ^ 3 * ((1 / 6 - c3) + Z * (1 / 24 - c4) + c4 * zl)| ≤
      R ^ 3 * (|1 / 6 - c3| + R * |1 / 24 - c4| + c4 * Lz) := by
    rw [abs_mul]; exact mul_le_mul hZ3 hin (abs_nonneg _) (by positivity)
  have k2 : |Real.exp Z - (1 + Z + Z ^ 2 / 2 + Z ^ 3 / 6 + Z ^ 4 / 24)| ≤ R ^ 5 * (1 / 100) :=
    ht.trans (mul_le_mul_of_nonneg_right hZ5 (by norm_num))
  linarith

#print axioms q1_exp

#print axioms q1_core_pr

end Verified.Examples.ErfcQ1
