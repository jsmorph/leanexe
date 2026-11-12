import Demos.Attitude.Model

/-! The deterministic error bound of TRIAD.  For observations whose images under the true attitude
lie within `ε1` and `ε2` of their references, `triad_error` bounds the angle between TRIAD's
image and the true image of every unit vector by `2 arcsin √h`, with `h = hval ε1 ε2 (sin θ)`.

The proof follows the derivation of the requirements.  `triad_reduce` moves the problem to the
inertial frame: TRIAD's attitude is the map `E` from the frame of `u_i = R(q) b̄_i` to the frame of
the references, after `R(q)`.  `core` writes `E` as the action of the product of two quaternions:
`turn u1 r1`, which rotates `u1` onto `r1`, and `turn a s2`, which rotates about `r1`.  Their
vector parts are perpendicular, so the scalar part of the product is the product of the scalar
parts, and the bound on the second factor comes from the Cauchy–Schwarz inequality in the plane
and the triangle inequality for angles. -/

namespace Demos.Attitude

open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Normalize Demos.Slew.Rotation Demos.Slew.Safety
open Demos.Slew.Premise Vec Real

/-- The quantity `h` of the bound: with `x = sin (ε1 + ε2) / sθ`,
`h = sin²(ε1/2) + cos²(ε1/2) · x² / (2 (1 + √(1 - x²)))`. -/
noncomputable def hval (e1 e2 st : ℝ) : ℝ :=
  sin (e1 / 2) ^ 2 + cos (e1 / 2) ^ 2 *
    ((sin (e1 + e2) / st) ^ 2 / (2 * (1 + √(1 - (sin (e1 + e2) / st) ^ 2))))

/-- The quaternion `(1 + a · b, a × b)`, which rotates the unit vector `a` onto `b`. -/
def turn (a b : Vec) : Quat := ⟨1 + dot a b, (cross a b).x, (cross a b).y, (cross a b).z⟩

/-! ### Quaternion actions -/

theorem act_smul (q : Quat) (k : ℝ) (v : Vec) : act q (smul k v) = smul k (act q v) := by
  ext <;> simp only [act, vpart, qmul, conj, Demos.Slew.Rotation.pure, smul] <;> ring

theorem act_comb (q : Quat) (c1 c2 c3 : ℝ) (a b c : Vec) :
    act q (comb c1 c2 c3 a b c) = comb c1 c2 c3 (act q a) (act q b) (act q c) := by
  ext <;> simp only [act, vpart, qmul, conj, Demos.Slew.Rotation.pure, comb] <;> ring

theorem dot_act (q : Quat) (a b : Vec) :
    dot (act q a) (act q b) = Quat.norm2 q ^ 2 * dot a b := by
  simp only [dot, act, vpart, qmul, conj, Demos.Slew.Rotation.pure, Quat.norm2]; ring

theorem act_cross (q : Quat) (a b : Vec) :
    smul (Quat.norm2 q) (act q (cross a b)) = cross (act q a) (act q b) := by
  ext <;> simp only [act, vpart, qmul, conj, Demos.Slew.Rotation.pure, cross, smul, Quat.norm2] <;>
    ring

theorem dot_act_self (q : Quat) (v : Vec) :
    dot v (act q v) = (q.w ^ 2 - (q.x ^ 2 + q.y ^ 2 + q.z ^ 2)) * dot v v +
      2 * (q.x * v.x + q.y * v.y + q.z * v.z) ^ 2 := by
  simp only [dot, act, vpart, qmul, conj, Demos.Slew.Rotation.pure]; ring

/-- A rotation moves a vector at most by the angle that its scalar part gives. -/
theorem dot_act_self_ge (q : Quat) (v : Vec) :
    (2 * q.w ^ 2 - Quat.norm2 q) * dot v v ≤ dot v (act q v) := by
  rw [dot_act_self]
  have : 2 * q.w ^ 2 - Quat.norm2 q = q.w ^ 2 - (q.x ^ 2 + q.y ^ 2 + q.z ^ 2) := by
    simp only [Quat.norm2]; ring
  rw [this]
  nlinarith [sq_nonneg (q.x * v.x + q.y * v.y + q.z * v.z)]

theorem norm2_turn {a b : Vec} (ha : dot a a = 1) (hb : dot b b = 1) :
    Quat.norm2 (turn a b) = 2 * (1 + dot a b) := by
  have e := dot_cross_self a b
  simp only [Quat.norm2, turn]
  simp only [dot] at e ha hb ⊢
  rw [ha, hb] at e
  nlinarith [e]

/-- `turn a b` rotates `a` onto `b`, scaled by its squared norm. -/
theorem act_turn {a b : Vec} (ha : dot a a = 1) (hb : dot b b = 1) :
    act (turn a b) a = smul (2 * (1 + dot a b)) b := by
  simp only [dot] at ha hb
  ext <;> simp only [act, vpart, qmul, conj, Demos.Slew.Rotation.pure, turn, smul, dot, cross]
  · linear_combination (a.x * b.x ^ 2 - a.x * b.y ^ 2 - a.x * b.z ^ 2 + 2 * a.y * b.x * b.y +
      2 * a.z * b.x * b.z + 2 * b.x) * ha + (-a.x) * hb
  · linear_combination (2 * a.x * b.x * b.y - a.y * b.x ^ 2 + a.y * b.y ^ 2 - a.y * b.z ^ 2 +
      2 * a.z * b.y * b.z + 2 * b.y) * ha + (-a.y) * hb
  · linear_combination (2 * a.x * b.x * b.z + 2 * a.y * b.y * b.z - a.z * b.x ^ 2 -
      a.z * b.y ^ 2 + a.z * b.z ^ 2 + 2 * b.z) * ha + (-a.z) * hb

/-- A quaternion whose vector part is a multiple of `r` fixes `r`, scaled by its squared norm. -/
theorem act_axis (w k : ℝ) (r : Vec) :
    act ⟨w, k * r.x, k * r.y, k * r.z⟩ r = smul (w ^ 2 + k ^ 2 * dot r r) r := by
  ext <;> simp only [act, vpart, qmul, conj, Demos.Slew.Rotation.pure, smul, dot] <;> ring

/-- The cross product of two vectors perpendicular to a unit `r` is a multiple of `r`. -/
theorem cross_perp {a b r : Vec} (ha : dot a r = 0) (hb : dot b r = 0) (hr : dot r r = 1) :
    cross a b = smul (dot (cross a b) r) r := by
  simp only [dot] at ha hb hr
  ext <;> simp only [cross, smul, dot]
  · linear_combination (-(a.y * b.z - a.z * b.y)) * hr + (a.y * r.z - a.z * r.y) * hb -
      (b.y * r.z - b.z * r.y) * ha
  · linear_combination (-(a.z * b.x - a.x * b.z)) * hr + (a.z * r.x - a.x * r.z) * hb -
      (b.z * r.x - b.x * r.z) * ha
  · linear_combination (-(a.x * b.y - a.y * b.x)) * hr + (a.x * r.y - a.y * r.x) * hb -
      (b.x * r.y - b.y * r.x) * ha

theorem act_turn_axis {a b r : Vec} (ha : dot a r = 0) (hb : dot b r = 0) (hr : dot r r = 1) :
    act (turn a b) r = smul (Quat.norm2 (turn a b)) r := by
  have e := cross_perp ha hb hr
  have hq : turn a b = ⟨1 + dot a b, dot (cross a b) r * r.x, dot (cross a b) r * r.y,
      dot (cross a b) r * r.z⟩ := by
    simp only [turn]
    conv_lhs => rw [e]
    rfl
  rw [hq, act_axis]
  congr 1
  simp only [Quat.norm2, dot]
  ring

/-! ### Angles and cosines -/

theorem norm_one_of {a : Vec} (h : dot a a = 1) : norm a = 1 := norm_eq_one_of a h

theorem abs_dot_le_one {a b : Vec} (ha : dot a a = 1) (hb : dot b b = 1) : |dot a b| ≤ 1 := by
  have := abs_dot_le a b
  rwa [norm_one_of ha, norm_one_of hb, one_mul] at this

theorem cos_le_dot {a b : Vec} (ha : dot a a = 1) (hb : dot b b = 1) {ε : ℝ} (hε : ε ≤ π)
    (h : vangle a b ≤ ε) : cos ε ≤ dot a b := by
  rw [vangle_eq (norm_one_of ha) (norm_one_of hb)] at h
  have hab := abs_le.mp (abs_dot_le_one ha hb)
  calc cos ε ≤ cos (arccos (dot a b)) :=
        cos_le_cos_of_nonneg_of_le_pi (arccos_nonneg _) hε h
    _ = dot a b := cos_arccos hab.1 hab.2

theorem vangle_le {a b : Vec} (ha : dot a a = 1) (hb : dot b b = 1) {ε : ℝ} (h0 : 0 ≤ ε)
    (hε : ε ≤ π) (h : cos ε ≤ dot a b) : vangle a b ≤ ε := by
  rw [vangle_eq (norm_one_of ha) (norm_one_of hb)]
  calc arccos (dot a b) ≤ arccos (cos ε) := arccos_le_arccos h
    _ = ε := arccos_cos h0 hε

/-! ### The core inequality -/

/-- `1 - 2h` in terms of `cos ε1` and `√(1 - x²)`. -/
theorem one_sub_two_hval {e1 e2 st : ℝ} (hx : (sin (e1 + e2) / st) ^ 2 ≤ 1) :
    1 - 2 * hval e1 e2 st =
      (1 + √(1 - (sin (e1 + e2) / st) ^ 2)) * (1 + cos e1) / 2 - 1 := by
  rw [hval]
  set x := sin (e1 + e2) / st
  set s := √(1 - x ^ 2)
  have hss : s ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (by linarith)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hxs : x ^ 2 / (2 * (1 + s)) = (1 - s) / 2 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]; linear_combination 2 * hss
  have hc : cos (e1 / 2) ^ 2 = 1 / 2 + cos e1 / 2 := by
    rw [cos_sq]; congr 3; ring
  have hsc := sin_sq_add_cos_sq (e1 / 2)
  rw [hxs]
  linear_combination (1 + s) * hc - 2 * hsc

/-- The inequality of the derivation in the inertial frame.  For unit vectors `u_i` within `ε_i`
of unit references `r_i`, the map from the frame of the `u_i` to the frame of the `r_i` moves
every unit vector `y` by an angle whose cosine is at least `1 - 2h`. -/
theorem core {u1 u2 r1 r2 : Vec} (hu1 : dot u1 u1 = 1) (hu2 : dot u2 u2 = 1)
    (hr1 : dot r1 r1 = 1) (hr2 : dot r2 r2 = 1) {ε1 ε2 : ℝ} (he1 : 0 ≤ ε1) (he2 : 0 ≤ ε2)
    (hd : ε1 + ε2 < π / 2) (hx : sin (ε1 + ε2) < norm (cross r1 r2))
    (h1 : vangle u1 r1 ≤ ε1) (h2 : vangle u2 r2 ≤ ε2) :
    0 < norm (cross u1 u2) ∧ ∀ y : Vec, dot y y = 1 →
      1 - 2 * hval ε1 ε2 (norm (cross r1 r2)) ≤
        dot y (Frame.map (frame u1 u2) (frame r1 r2) y) := by
  have hpi := pi_pos
  -- the cosine of the first hypothesis
  have hc1 : cos ε1 ≤ dot u1 r1 := cos_le_dot hu1 hr1 (by linarith) h1
  have hcos1 : 0 < cos ε1 := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  set c := dot u1 r1 with hc_def
  have hcp : 0 < 1 + c := by linarith
  -- the first quaternion carries u1 onto r1
  set NM := 2 * (1 + c) with hNM_def
  have hNMp : 0 < NM := by positivity
  set qM := turn u1 r1 with hqM
  have hNM : Quat.norm2 qM = NM := norm2_turn hu1 hr1
  have hMu1 : act qM u1 = smul NM r1 := act_turn hu1 hr1
  set g := smul (1 / NM) (act qM u2) with hg_def
  have hu2g : act qM u2 = smul NM g := by
    rw [hg_def, smul_smul, mul_one_div_cancel hNMp.ne', smul_one]
  have hgg : dot g g = 1 := by
    rw [hg_def, dot_smul_left, dot_smul_right, dot_act, hNM, hu2]
    field_simp
  have hgu2 : c ≤ dot g u2 := by
    have h := dot_act_self_ge qM u2
    rw [hNM, hu2, show qM.w = 1 + c from rfl] at h
    rw [hg_def, dot_smul_left, dot_comm (act qM u2) u2, div_mul_eq_mul_div, one_mul,
      le_div_iff₀ hNMp]
    have e : c * NM = (2 * (1 + c) ^ 2 - NM) * 1 := by rw [hNM_def]; ring
    linarith
  -- g lies within ε1 + ε2 of r2
  have hgr2 : cos (ε1 + ε2) ≤ dot g r2 := by
    have a1 : vangle g u2 ≤ ε1 := vangle_le hgg hu2 he1 (by linarith) (hc1.trans hgu2)
    have a2 := vangle_triangle g u2 r2
    exact cos_le_dot hgg hr2 (by linarith) (by linarith)
  -- the references
  set C := dot r1 r2 with hC_def
  set sθ := norm (cross r1 r2) with hsθ_def
  have hsθ2 : sθ ^ 2 = 1 - C ^ 2 := by
    rw [sq, norm_sq, dot_cross_self, hr1, hr2, ← hC_def]; ring
  have hsθ0 : 0 ≤ sθ := norm_nonneg _
  set sd := sin (ε1 + ε2) with hsd_def
  set cd := cos (ε1 + ε2) with hcd_def
  have hsd0 : 0 ≤ sd := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hcd0 : 0 < cd := cos_pos_of_mem_Ioo ⟨by linarith, hd⟩
  have hpyth : sd ^ 2 + cd ^ 2 = 1 := sin_sq_add_cos_sq _
  have hsθp : 0 < sθ := lt_of_le_of_lt hsd0 hx
  have hCcd : C ^ 2 < cd ^ 2 := by
    have := mul_self_lt_mul_self hsd0 hx
    nlinarith
  -- the angle about r1
  set C' := dot r1 g with hC'_def
  have hBC : dot (cross r1 g) (cross r1 r2) = dot g r2 - C * C' := by
    rw [dot_cross_cross, hr1, dot_comm g r1]; ring
  set S' := norm (cross r1 g) with hS'_def
  have hS'2 : S' ^ 2 = 1 - C' ^ 2 := by
    rw [sq, norm_sq, dot_cross_self, hr1, hgg, ← hC'_def]; ring
  have hS'0 : 0 ≤ S' := norm_nonneg _
  have hCS : (dot g r2 - C * C') ^ 2 ≤ S' ^ 2 * sθ ^ 2 := by
    have h := dot_sq_le (cross r1 g) (cross r1 r2)
    rw [hBC, ← norm_sq, ← norm_sq] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  have hC'1 : C' ^ 2 ≤ 1 := by linarith [hS'2, sq_nonneg S']
  have hS'p : 0 < S' := by
    by_contra hne
    have h0 : S' = 0 := le_antisymm (not_lt.mp hne) hS'0
    rw [h0] at hCS
    have hle : (dot g r2 - C * C') ^ 2 ≤ 0 := by simpa using hCS
    have heq : (dot g r2 - C * C') ^ 2 = 0 := le_antisymm hle (sq_nonneg _)
    have heq' : dot g r2 = C * C' := by
      have := (pow_eq_zero_iff two_ne_zero).mp heq
      linarith
    have h3 : cd * cd ≤ dot g r2 * dot g r2 := mul_self_le_mul_self hcd0.le hgr2
    have h4 : C ^ 2 * C' ^ 2 ≤ C ^ 2 * 1 := mul_le_mul_of_nonneg_left hC'1 (sq_nonneg C)
    rw [heq'] at h3
    have e1 : C * C' * (C * C') = C ^ 2 * C' ^ 2 := by ring
    have e2 : cd * cd = cd ^ 2 := by ring
    linarith
  set K := √(cd ^ 2 - C ^ 2) with hK_def
  have hK0 : 0 ≤ K := Real.sqrt_nonneg _
  have hKK : K ^ 2 = cd ^ 2 - C ^ 2 := Real.sq_sqrt (by linarith)
  have hplane : C * C' + S' * K ≤ cd := by
    have e : (C * C' + S' * K) ^ 2 = (C ^ 2 + K ^ 2) * (C' ^ 2 + S' ^ 2) - (C * S' - K * C') ^ 2 := by
      ring
    have e2 : (C ^ 2 + K ^ 2) * (C' ^ 2 + S' ^ 2) = cd ^ 2 := by rw [hKK, hS'2]; ring
    have hsq : (C * C' + S' * K) ^ 2 ≤ cd ^ 2 := by
      rw [e, e2]; linarith [sq_nonneg (C * S' - K * C')]
    exact (abs_le_of_sq_le_sq' hsq hcd0.le).2
  -- the unit vectors a and s2
  set a := smul (1 / S') (cross r1 g) with ha_def
  have haa : dot a a = 1 := by
    rw [ha_def, dot_smul_left, dot_smul_right, ← norm_sq, ← hS'_def]; field_simp
  have har1 : dot a r1 = 0 := by rw [ha_def, dot_smul_left, dot_comm, dot_cross_left]; ring
  have hs2_def : (frame r1 r2).e2 = smul (1 / sθ) (cross r1 r2) := rfl
  set s2 := (frame r1 r2).e2 with hs2_set
  have hs2s2 : dot s2 s2 = 1 := dot_unit_self hsθp
  have hs2r1 : dot s2 r1 = 0 := by rw [hs2_def, dot_smul_left, dot_comm, dot_cross_left]; ring
  have has2 : dot a s2 = (dot g r2 - C * C') / (S' * sθ) := by
    rw [ha_def, hs2_def, dot_smul_left, dot_smul_right, hBC]; field_simp
  have has2_ge : K / sθ ≤ dot a s2 := by
    rw [has2, div_le_div_iff₀ hsθp (by positivity)]
    have : S' * K ≤ dot g r2 - C * C' := by linarith
    calc K * (S' * sθ) = (S' * K) * sθ := by ring
      _ ≤ (dot g r2 - C * C') * sθ := mul_le_mul_of_nonneg_right this hsθp.le
  have hKs : 0 ≤ K / sθ := by positivity
  have hP : 0 < 1 + dot a s2 := by linarith
  -- the second quaternion rotates about r1
  set NP := 2 * (1 + dot a s2) with hNP_def
  have hNPp : 0 < NP := by positivity
  set qP := turn a s2 with hqP
  have hNP : Quat.norm2 qP = NP := norm2_turn haa hs2s2
  have hPa : act qP a = smul NP s2 := act_turn haa hs2s2
  have hPr1 : act qP r1 = smul NP r1 := by rw [act_turn_axis har1 hs2r1 hr1, hNP]
  -- the frame of the u_i
  have hT1 : (frame u1 u2).e1 = u1 := unit_of_dot_one hu1
  have hMc : act qM (cross u1 u2) = smul NM (cross r1 g) := by
    have h := act_cross qM u1 u2
    rw [hNM, hMu1, hu2g, cross_smul_left, cross_smul_right, smul_smul] at h
    have h' := congrArg (smul (1 / NM)) h
    rw [smul_smul, smul_smul, one_div_mul_cancel hNMp.ne', smul_one] at h'
    rw [h']
    congr 1
    field_simp
  have hnorm : norm (cross u1 u2) = S' := by
    have h := norm_act qM (cross u1 u2)
    rw [hMc, Demos.Slew.Arc.norm_smul, hNM, abs_of_pos hNMp] at h
    exact (mul_left_cancel₀ hNMp.ne' h).symm
  have hcu : 0 < norm (cross u1 u2) := hnorm ▸ hS'p
  have gT := frame_good (norm_pos_of_dot (by rw [hu1]; norm_num)) hcu
  have hMt2 : act qM (frame u1 u2).e2 = smul NM a := by
    show act qM (smul (1 / norm (cross u1 u2)) (cross u1 u2)) = _
    rw [act_smul, hMc, hnorm, ha_def, smul_smul, smul_smul, mul_comm]
  -- the product of the two quaternions
  set qE := qmul qP qM with hqE
  have hE : ∀ v, act qE v = act qP (act qM v) := fun v => act_qmul qP qM v
  set N := NP * NM with hN_def
  have hNp : 0 < N := by positivity
  have hN : Quat.norm2 qE = N := by rw [hqE, norm2_qmul, hNP, hNM]
  have gS := frame_good (norm_pos_of_dot (by rw [hr1]; norm_num)) hsθp
  have hS1 : (frame r1 r2).e1 = r1 := unit_of_dot_one hr1
  have hEt1 : act qE (frame u1 u2).e1 = smul N (frame r1 r2).e1 := by
    rw [hE, hT1, hMu1, act_smul, hPr1, smul_smul, hS1, mul_comm]
  have hEt2 : act qE (frame u1 u2).e2 = smul N (frame r1 r2).e2 := by
    rw [hE, hMt2, act_smul, hPa, smul_smul, mul_comm]
  have hEt3 : act qE (frame u1 u2).e3 = smul N (frame r1 r2).e3 := by
    have h := act_cross qE (frame u1 u2).e1 (frame u1 u2).e2
    rw [← gT.e3, hN, hEt1, hEt2, cross_smul_left, cross_smul_right, smul_smul, ← gS.e3] at h
    have h' := congrArg (smul (1 / N)) h
    rw [smul_smul, smul_smul, one_div_mul_cancel hNp.ne', smul_one] at h'
    rw [h']
    congr 1
    field_simp
  have hEy : ∀ y, act qE y = smul N (Frame.map (frame u1 u2) (frame r1 r2) y) := by
    intro y
    conv_lhs => rw [← gT.expand y]
    rw [act_comb, hEt1, hEt2, hEt3, Frame.map]
    ext <;> simp only [comb, smul] <;> ring
  -- the scalar part of the product
  have hw : qE.w = (1 + dot a s2) * (1 + c) := by
    have h := dot_cross_cross a s2 u1 r1
    rw [har1, hs2r1] at h
    have e : qE.w = (1 + dot a s2) * (1 + dot u1 r1) - dot (cross a s2) (cross u1 r1) := by
      simp only [hqE, qmul, hqP, hqM, turn, dot]; ring
    rw [e, h]; ring
  refine ⟨hcu, fun y hy => ?_⟩
  have hge := dot_act_self_ge qE y
  rw [hy, hN, hw, hEy, dot_smul_right] at hge
  have hmain : (1 + dot a s2) * (1 + c) / 2 - 1 ≤
      dot y (Frame.map (frame u1 u2) (frame r1 r2) y) := by
    have e : (1 + dot a s2) * (1 + c) / 2 - 1 =
        (2 * ((1 + dot a s2) * (1 + c)) ^ 2 - N) * 1 / N := by
      rw [hN_def, hNP_def, hNM_def]; field_simp
    rw [e, div_le_iff₀ hNp, mul_comm (dot y _) N]
    exact hge
  have hx2 : (sd / sθ) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity), sq, sq]
    exact (mul_self_lt_mul_self hsd0 hx).le
  rw [one_sub_two_hval hx2]
  have hsq : √(1 - (sd / sθ) ^ 2) = K / sθ := by
    have e : 1 - (sd / sθ) ^ 2 = (cd ^ 2 - C ^ 2) / sθ ^ 2 := by
      field_simp; linarith
    rw [e, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hsθ0]
  rw [hsq]
  have hm : (1 + K / sθ) * (1 + cos ε1) ≤ (1 + dot a s2) * (1 + c) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  linarith

/-! ### The reduction to the inertial frame -/

section Reduce

variable {Q : Quat}

theorem act_cross_one (hQ : Quat.norm2 Q = 1) (a b : Vec) :
    act Q (cross a b) = cross (act Q a) (act Q b) := by
  have h := act_cross Q a b
  rwa [hQ, smul_one] at h

theorem dot_act_one (hQ : Quat.norm2 Q = 1) (a b : Vec) : dot (act Q a) (act Q b) = dot a b := by
  rw [dot_act, hQ]; ring

theorem act_unit (hQ : Quat.norm2 Q = 1) (a : Vec) : act Q (unit a) = unit (act Q a) := by
  rw [unit, unit, act_smul, norm_act, hQ, one_mul]

/-- TRIAD's attitude is the map between the frame of the `u_i = Q b̄_i` and the frame of the
references, after `Q`. -/
theorem triad_reduce (hQ : Quat.norm2 Q = 1) {b1 b2 : Vec} (hb1 : 0 < norm b1)
    (hb2 : 0 < norm b2) (r1 r2 v : Vec) :
    triadMap b1 b2 r1 r2 v =
      Frame.map (frame (act Q (unit b1)) (act Q (unit b2))) (frame r1 r2) (act Q v) := by
  have e1 : (frame (act Q (unit b1)) (act Q (unit b2))).e1 = act Q (frame b1 b2).e1 := by
    show unit (act Q (unit b1)) = act Q (unit b1)
    rw [← act_unit hQ, unit_of_dot_one (dot_unit_self hb1)]
  have e2 : (frame (act Q (unit b1)) (act Q (unit b2))).e2 = act Q (frame b1 b2).e2 := by
    show unit (cross (act Q (unit b1)) (act Q (unit b2))) = act Q (unit (cross b1 b2))
    rw [← act_cross_one hQ, act_unit hQ, cross_unit_unit, act_smul]
    exact unit_smul (by positivity) _
  have e3 : (frame (act Q (unit b1)) (act Q (unit b2))).e3 = act Q (frame b1 b2).e3 := by
    show cross (frame (act Q (unit b1)) (act Q (unit b2))).e1
      (frame (act Q (unit b1)) (act Q (unit b2))).e2 = act Q (cross (frame b1 b2).e1 (frame b1 b2).e2)
    rw [e1, e2, act_cross_one hQ]
  simp only [triadMap, Frame.map]
  rw [e1, e2, e3, dot_act_one hQ, dot_act_one hQ, dot_act_one hQ]

end Reduce

theorem frame_unit {a b : Vec} (ha : 0 < norm a) (hb : 0 < norm b) :
    frame (unit a) (unit b) = frame a b := by
  have e1 : unit (unit a) = unit a := unit_of_dot_one (dot_unit_self ha)
  have e2 : unit (cross (unit a) (unit b)) = unit (cross a b) := unit_cross_unit ha hb
  simp only [frame, e1, e2]

/-- `cos (2 arcsin √h) = 1 - 2h` for `h` in `[0, 1]`. -/
theorem cos_two_arcsin_sqrt {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    cos (2 * arcsin √h) = 1 - 2 * h := by
  have hs1 : √h ≤ 1 := Real.sqrt_le_one.mpr h1
  have hsin : sin (arcsin √h) = √h := sin_arcsin (by linarith [Real.sqrt_nonneg h]) hs1
  rw [cos_two_mul, cos_sq', hsin, Real.sq_sqrt h0]; ring

theorem hval_nonneg {e1 e2 st : ℝ} : 0 ≤ hval e1 e2 st := by
  rw [hval]
  have : 0 ≤ 1 + √(1 - (sin (e1 + e2) / st) ^ 2) := by positivity
  positivity

theorem hval_le_one {e1 e2 st : ℝ} (hx : (sin (e1 + e2) / st) ^ 2 ≤ 1) (hc : 0 ≤ 1 + cos e1) :
    hval e1 e2 st ≤ 1 := by
  have e := one_sub_two_hval hx
  have : 0 ≤ (1 + √(1 - (sin (e1 + e2) / st) ^ 2)) * (1 + cos e1) := by positivity
  linarith

/-- **TRIAD's error bound.**  Let the true attitude `R(q)` carry the normalized measurements to
within `ε1` and `ε2` of the normalized references, with `ε1, ε2 ≥ 0`, `ε1 + ε2 < π/2`, and
`sin (ε1 + ε2) < sin θ`, where `sin θ = |r̄1 × r̄2|`.  Then TRIAD's attitude moves no unit vector
farther than `2 arcsin √h` from its image under `R(q)`. -/
theorem triad_error {b1 b2 r1 r2 : Vec} (hb1 : 0 < norm b1) (hb2 : 0 < norm b2)
    (hr1 : 0 < norm r1) (hr2 : 0 < norm r2) {ε1 ε2 : ℝ} (he1 : 0 ≤ ε1) (he2 : 0 ≤ ε2)
    (hd : ε1 + ε2 < π / 2) (hx : sin (ε1 + ε2) < norm (cross (unit r1) (unit r2)))
    {q : Quat} (hq : 0 < Quat.norm2 q)
    (h1 : vangle (attitude q (unit b1)) (unit r1) ≤ ε1)
    (h2 : vangle (attitude q (unit b2)) (unit r2) ≤ ε2) {v : Vec} (hv : dot v v = 1) :
    vangle (triadMap b1 b2 r1 r2 v) (attitude q v) ≤
      2 * arcsin √(hval ε1 ε2 (norm (cross (unit r1) (unit r2)))) := by
  have hpi := pi_pos
  set Q := Quat.unit q
  have hQ : Quat.norm2 Q = 1 := norm2_unit q hq
  rw [attitude_eq hq] at h1 h2 ⊢
  have hu1 : dot (act Q (unit b1)) (act Q (unit b1)) = 1 := by
    rw [dot_act_one hQ, dot_unit_self hb1]
  have hu2 : dot (act Q (unit b2)) (act Q (unit b2)) = 1 := by
    rw [dot_act_one hQ, dot_unit_self hb2]
  obtain ⟨hcu, hcore⟩ := core hu1 hu2 (dot_unit_self hr1) (dot_unit_self hr2) he1 he2 hd hx h1 h2
  set y := act Q v
  have hy : dot y y = 1 := by rw [dot_act_one hQ, hv]
  have hE := hcore y hy
  rw [triad_reduce hQ hb1 hb2, ← frame_unit hr1 hr2]
  set st := norm (cross (unit r1) (unit r2))
  have hsd0 : 0 ≤ sin (ε1 + ε2) := sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  have hst : 0 < st := lt_of_le_of_lt hsd0 hx
  have gT := frame_good (norm_pos_of_dot (by rw [hu1]; norm_num)) hcu
  have gS := frame_good (norm_pos_of_dot (by rw [dot_unit_self hr1]; norm_num)) hst
  have hEE : dot (Frame.map (frame (act Q (unit b1)) (act Q (unit b2)))
      (frame (unit r1) (unit r2)) y) (Frame.map (frame (act Q (unit b1)) (act Q (unit b2)))
      (frame (unit r1) (unit r2)) y) = 1 := by rw [map_dot gT gS, hy]
  have hx2 : (sin (ε1 + ε2) / st) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity), sq, sq]
    exact (mul_self_lt_mul_self hsd0 hx).le
  have hc1 : 0 ≤ 1 + cos ε1 := by linarith [neg_one_le_cos ε1]
  have hh0 := hval_nonneg (e1 := ε1) (e2 := ε2) (st := st)
  have hh1 := hval_le_one hx2 hc1
  have hs1 : √(hval ε1 ε2 st) ≤ 1 := Real.sqrt_le_one.mpr hh1
  have ha0 : 0 ≤ arcsin √(hval ε1 ε2 st) := arcsin_nonneg.mpr (Real.sqrt_nonneg _)
  have ha1 : arcsin √(hval ε1 ε2 st) ≤ π / 2 := arcsin_le_pi_div_two _
  apply vangle_le hEE hy (by linarith) (by linarith)
  rw [cos_two_arcsin_sqrt hh0 hh1, dot_comm]
  exact hE

theorem map_smul (t s : Frame) (k : ℝ) (v : Vec) :
    Frame.map t s (smul k v) = smul k (Frame.map t s v) := by
  ext <;> simp only [Frame.map, comb, smul, dot] <;> ring

/-- Two unit vectors at angle zero are equal. -/
theorem eq_of_vangle_zero {a b : Vec} (ha : dot a a = 1) (hb : dot b b = 1)
    (h : vangle a b ≤ 0) : a = b := by
  have hab := abs_le.mp (abs_dot_le_one ha hb)
  have h1 : cos 0 ≤ dot a b := cos_le_dot ha hb (by linarith [pi_pos]) h
  rw [cos_zero] at h1
  have hd : dot (sub a b) (sub a b) = 0 := by
    have e : dot (sub a b) (sub a b) = dot a a - 2 * dot a b + dot b b := by
      simp only [dot, sub]; ring
    rw [e]; linarith
  simp only [dot, sub] at hd
  ext
  · nlinarith [sq_nonneg (a.x - b.x), sq_nonneg (a.y - b.y), sq_nonneg (a.z - b.z)]
  · nlinarith [sq_nonneg (a.x - b.x), sq_nonneg (a.y - b.y), sq_nonneg (a.z - b.z)]
  · nlinarith [sq_nonneg (a.x - b.x), sq_nonneg (a.y - b.y), sq_nonneg (a.z - b.z)]

/-- **TRIAD recovers an attitude that maps both measurements onto their references.** -/
theorem triad_exact {b1 b2 r1 r2 : Vec} (hb1 : 0 < norm b1) (hb2 : 0 < norm b2)
    (hb : 0 < norm (cross b1 b2)) (hr1 : 0 < norm r1) (hr2 : 0 < norm r2)
    (hr : 0 < norm (cross r1 r2)) {q : Quat} (hq : 0 < Quat.norm2 q)
    (h1 : attitude q (unit b1) = unit r1) (h2 : attitude q (unit b2) = unit r2) (v : Vec) :
    triadMap b1 b2 r1 r2 v = attitude q v := by
  have hpi := pi_pos
  have hst : 0 < norm (cross (unit r1) (unit r2)) := by
    rw [cross_unit_unit, Demos.Slew.Arc.norm_smul, abs_of_pos (by positivity)]; positivity
  have hz : vangle (unit r1) (unit r1) ≤ 0 := by
    rw [vangle_eq (norm_unit r1 hr1) (norm_unit r1 hr1), dot_unit_self hr1, arccos_one]
  have hz2 : vangle (unit r2) (unit r2) ≤ 0 := by
    rw [vangle_eq (norm_unit r2 hr2) (norm_unit r2 hr2), dot_unit_self hr2, arccos_one]
  have hunit : ∀ w : Vec, dot w w = 1 → triadMap b1 b2 r1 r2 w = attitude q w := by
    intro w hw
    have h := triad_error hb1 hb2 hr1 hr2 le_rfl le_rfl (by linarith)
      (by rw [add_zero, sin_zero]; exact hst) hq (by rw [h1]; exact hz) (by rw [h2]; exact hz2) hw
    have h0 : hval 0 0 (norm (cross (unit r1) (unit r2))) = 0 := by simp [hval]
    rw [h0, Real.sqrt_zero, arcsin_zero, mul_zero] at h
    have hT : dot (triadMap b1 b2 r1 r2 w) (triadMap b1 b2 r1 r2 w) = 1 := by
      rw [triad_dot hb1 hb hr1 hr, hw]
    have hA : dot (attitude q w) (attitude q w) = 1 := by
      rw [← norm_sq, norm_attitude hq, norm_sq, hw]
    exact eq_of_vangle_zero hT hA h
  by_cases hv : norm v = 0
  · have hv0 : v = ⟨0, 0, 0⟩ := by
      have := dot_self_nonneg v
      have hd : dot v v = 0 := by rw [← norm_sq, hv, mul_zero]
      simp only [dot] at hd
      ext <;> simp <;> nlinarith [sq_nonneg v.x, sq_nonneg v.y, sq_nonneg v.z]
    subst hv0
    ext <;> simp [triadMap, Frame.map, comb, dot, attitude, Quat.rot]
  · have hvp : 0 < norm v := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
    have e : v = smul (norm v) (unit v) := by
      rw [unit, smul_smul, mul_one_div_cancel hv, smul_one]
    rw [e, triadMap, map_smul, ← triadMap, attitude, rot_smul_right, ← attitude,
      hunit _ (dot_unit_self hvp)]

end Demos.Attitude
