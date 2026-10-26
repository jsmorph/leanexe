import Demos.Slew.Search
import Demos.Slew.Angle

/-! The safety theorem of the slew planner.  For an output of status 1, `plan_safe` states that
the plan starts at the input's start attitude and ends at its goal, bit for bit; that each
segment's commanded rotation, by its output angle about its output axis, carries its start
attitude to within `1e-9` of the next segment's start attitude, or the goal's; and that every
attitude within `1e-9` of the commanded path satisfies every cone of the input.  An attitude `R`
lies within `ρ` of an attitude `R'` when it moves no unit vector farther than `ρ` from `R'`.

The proof joins the path structure of the search (`plan_segments`), which makes every segment
an edge that `edgeOk` accepted, with the soundness of the edge check (`edgeOk_sound`), whose
hypotheses come from `validInput` (`valid_good`) and `relative` (`relative_good`).  The output's
axis and angle lie within `5e-14` of the axis and angle of the relative quaternion's real value
(`angle_out`, `axis_out`), and the rotation by that axis and angle carries the start attitude to
within `1.2e-14` of the next node (`relative_rot`).  The margin's tube of `1.05e-9` absorbs
these differences (`segment_safe`). -/

namespace Demos.Slew.Safety

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error Demos.Slew.Axis Demos.Slew.Cone
open Demos.Slew.Normalize Demos.Slew.Arc Demos.Slew.Decide Demos.Slew.Check Demos.Slew.Rotation
open Demos.Slew.Relative Demos.Slew.Valid Demos.Slew.Angle Demos.Slew.Search Real
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- The attitude `R(q̄)` of a quaternion `q`: the rotation formula on `q` normalized. -/
noncomputable def attitude (q : Quat) (v : Vec) : Vec := Quat.rot (Quat.unit q) v

/-- The real quaternion and the real vector stored at offset `o` of an output. -/
noncomputable def quatAt (out : Array Float) (o : Nat) : Quat :=
  ⟨val out[o]!, val out[o + 1]!, val out[o + 2]!, val out[o + 3]!⟩

noncomputable def vecAt (out : Array Float) (o : Nat) : Vec :=
  ⟨val out[o]!, val out[o + 1]!, val out[o + 2]!⟩

/-- The output axis of a segment with relative quaternion `rel`. -/
noncomputable def axisOut (rel : Q4) : Vec :=
  if Demos.Slew.axisMin ≤ sOf rel then
    ⟨val (rel.x / sOf rel), val (rel.y / sOf rel), val (rel.z / sOf rel)⟩
  else ⟨1, 0, 0⟩

/-! ### Rotations -/

theorem norm_act (q : Quat) (v : Vec) : Vec.norm (act q v) = Quat.norm2 q * Vec.norm v := by
  have e : Vec.dot (act q v) (act q v) = (Quat.norm2 q * Vec.norm v) ^ 2 := by
    rw [mul_pow, sq (Vec.norm v), norm_sq]
    simp only [Vec.dot, act, vpart, qmul, conj, Rotation.pure, Quat.norm2]; ring
  rw [Vec.norm, e, Real.sqrt_sq (mul_nonneg (norm2_nonneg q) (Arc.norm_nonneg v))]

theorem attitude_eq {q : Quat} (hq : 0 < Quat.norm2 q) (b : Vec) :
    attitude q b = act (Quat.unit q) b := rot_eq_act _ _ (norm2_unit q hq)

theorem norm_attitude {q : Quat} (hq : 0 < Quat.norm2 q) (b : Vec) :
    Vec.norm (attitude q b) = Vec.norm b := by
  rw [attitude_eq hq, norm_act, norm2_unit q hq, one_mul]

/-- Two Rodrigues rotations about unit axes move a vector apart by at most twice the sum of the
angle difference and the axis distance, times its length. -/
theorem rod_sub_le {n N : Vec} (hn : Vec.dot n n = 1) (hN : Vec.dot N N = 1) (φ φ' : ℝ)
    (X : Vec) :
    Vec.norm (Vec.sub (rod n φ X) (rod N φ' X)) ≤
      2 * (|φ - φ'| + Vec.norm (Vec.sub n N)) * Vec.norm X := by
  rw [rod_eq_act n φ X hn, rod_eq_act N φ' X hN]
  have h1 := act_sub_le (half n φ) (half N φ') X (norm2_half n φ hn) (norm2_half N φ' hN)
  have h2 := qnorm_half_sub_le n N φ φ' hn
  have hX := Arc.norm_nonneg X
  have := mul_le_mul_of_nonneg_right h2 hX
  nlinarith [qnorm_nonneg (qsub (half n φ) (half N φ'))]

theorem norm_sub_rev (a N : Vec) : Vec.norm a ≤ Vec.norm (Vec.sub a N) + Vec.norm N := by
  have h := norm_sub_le (Vec.sub a N) (Vec.smul (-1) N)
  have e : Vec.sub (Vec.sub a N) (Vec.smul (-1) N) = a := by
    ext <;> simp only [Vec.sub, Vec.smul] <;> ring
  rw [e, Arc.norm_smul, abs_neg, abs_one, one_mul] at h
  exact h

/-- Normalizing a vector near a unit vector at most doubles the distance. -/
theorem unit_close {a N : Vec} (hN : Vec.norm N = 1) (ha : 0 < Vec.norm a) :
    Vec.norm (Vec.sub (Vec.unit a) N) ≤ 2 * Vec.norm (Vec.sub a N) := by
  have h1 := norm_sub_triangle (Vec.unit a) a N
  rw [norm_unit_sub a ha] at h1
  have t1 := norm_sub_rev a N
  have t2 := norm_sub_rev N a
  rw [norm_sub_swap N a] at t2
  have : |1 - Vec.norm a| ≤ Vec.norm (Vec.sub a N) := by
    rw [abs_le]; constructor <;> linarith
  linarith

theorem dot_unit_x : Vec.dot (Vec.unit ⟨1, 0, 0⟩) (Vec.unit ⟨1, 0, 0⟩) = 1 := by
  have hn : Vec.norm (⟨1, 0, 0⟩ : Vec) = 1 := by
    rw [Vec.norm, show Vec.dot (⟨1, 0, 0⟩ : Vec) ⟨1, 0, 0⟩ = 1 by simp [Vec.dot], Real.sqrt_one]
  exact dot_unit_self _ (by rw [hn]; norm_num)

/-! ### One segment -/

/-- The commanded rotation of a segment stays within `5e-14 |X|` of a rotation by the axis and
an angle in the range of the relative quaternion's real value, and reaches within `5e-14 |X|`
of the rotation by its full angle. -/
theorem segment_close {rel : Q4} (hr : GoodRel rel) :
    Vec.dot (Vec.unit (axisOut rel)) (Vec.unit (axisOut rel)) = 1 ∧
    (∀ φ, 0 ≤ φ → φ ≤ val (angleOf rel) → ∃ φ', 0 ≤ φ' ∧ φ' ≤ angleR rel ∧ ∀ X : Vec,
      Vec.norm (Vec.sub (rod (Vec.unit (axisOut rel)) φ X) (rod (axisR rel) φ' X)) ≤
        5e-14 * Vec.norm X) ∧
    ∀ X : Vec, Vec.norm (Vec.sub (rod (Vec.unit (axisOut rel)) (val (angleOf rel)) X)
      (rod (axisR rel) (angleR rel) X)) ≤ 5e-14 * Vec.norm X := by
  obtain ⟨_, hθ⟩ := angle_out hr
  have hθa := abs_le.mp hθ
  have hθ0 := angle_nonneg (val rel.w) (√(s2 rel))
  have hθr : angleR rel = angle (val rel.w) (√(s2 rel)) := rfl
  obtain ⟨hbig, hsmall⟩ := axis_out hr
  by_cases hb : Demos.Slew.axisMin ≤ sOf rel
  · have hS2 := hbig hb
    have hSpos : 0 < √(s2 rel) := Real.sqrt_pos.mpr (lt_of_lt_of_le (by norm_num) hS2)
    obtain ⟨bx, byy, bz, _⟩ := hr.components
    have hsa := s_approx rel hr.fx hr.fy hr.fz (by linarith) (by linarith) (by linarith) hS2
    obtain ⟨cx, cy, cz⟩ := axis_bnd rel hr.fx hr.fy hr.fz hSpos hsa
    have hN : Vec.dot (axisR rel) (axisR rel) = 1 :=
      dot_unit_self (vecPart rel) (by rw [norm_vecPart]; exact hSpos)
    have hNn : Vec.norm (axisR rel) = 1 := norm_eq_one_of _ hN
    have hax : axisOut rel = ⟨val (rel.x / sOf rel), val (rel.y / sOf rel),
        val (rel.z / sOf rel)⟩ := by simp only [axisOut, hb, ite_true]
    have dx : |val (rel.x / sOf rel) - (axisR rel).x| ≤ 5.2 / 2 ^ 53 := cx.1.2
    have dy : |val (rel.y / sOf rel) - (axisR rel).y| ≤ 5.2 / 2 ^ 53 := cy.1.2
    have dz : |val (rel.z / sOf rel) - (axisR rel).z| ≤ 5.2 / 2 ^ 53 := cz.1.2
    have hd : Vec.norm (Vec.sub (axisOut rel) (axisR rel)) ≤ 9.1 / 2 ^ 53 := by
      rw [hax, Vec.norm, show (9.1 : ℝ) / 2 ^ 53 = √((9.1 / 2 ^ 53) ^ 2) by
        rw [Real.sqrt_sq (by norm_num)]]
      apply Real.sqrt_le_sqrt
      simp only [Vec.dot, Vec.sub]
      have sq : ∀ t : ℝ, |t| ≤ 5.2 / 2 ^ 53 → t * t ≤ (5.2 / 2 ^ 53) ^ 2 := by
        intro t ht; rw [← sq, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) ht 2
      have := sq _ dx
      have := sq _ dy
      have := sq _ dz
      nlinarith
    have hapos : 0 < Vec.norm (axisOut rel) := by
      have := norm_sub_rev (axisR rel) (axisOut rel)
      rw [norm_sub_swap (axisR rel) (axisOut rel), hNn] at this
      have : (9.1 : ℝ) / 2 ^ 53 < 1 / 2 := by norm_num
      linarith
    have hun := unit_close hNn hapos
    have hn1 : Vec.dot (Vec.unit (axisOut rel)) (Vec.unit (axisOut rel)) = 1 :=
      dot_unit_self _ hapos
    have hdist : Vec.norm (Vec.sub (Vec.unit (axisOut rel)) (axisR rel)) ≤ 18.2 / 2 ^ 53 := by
      linarith
    refine ⟨hn1, fun φ hφ0 hφ => ?_, fun X => ?_⟩
    · refine ⟨min φ (angleR rel), le_min hφ0 hθ0, min_le_right _ _, fun X => ?_⟩
      have hX := Arc.norm_nonneg X
      have hmin : |φ - min φ (angleR rel)| ≤ 1e-14 := by
        rcases le_total φ (angleR rel) with h | h
        · rw [min_eq_left h, sub_self, abs_zero]; norm_num
        · rw [min_eq_right h, abs_of_nonneg (by linarith)]; linarith
      have := rod_sub_le hn1 hN φ (min φ (angleR rel)) X
      have hk : 2 * (|φ - min φ (angleR rel)| + Vec.norm (Vec.sub (Vec.unit (axisOut rel))
          (axisR rel))) ≤ 5e-14 := by
        have : (18.2 : ℝ) / 2 ^ 53 ≤ 2.1e-15 := by norm_num
        linarith
      nlinarith
    · have hX := Arc.norm_nonneg X
      have := rod_sub_le hn1 hN (val (angleOf rel)) (angleR rel) X
      have hk : 2 * (|val (angleOf rel) - angleR rel| + Vec.norm (Vec.sub (Vec.unit (axisOut rel))
          (axisR rel))) ≤ 5e-14 := by
        have : (18.2 : ℝ) / 2 ^ 53 ≤ 2.1e-15 := by norm_num
        linarith
      nlinarith
  · have hS := hsmall hb
    have hax : axisOut rel = ⟨1, 0, 0⟩ := by simp only [axisOut, hb, ite_false]
    rw [hax]
    have hn1 := dot_unit_x
    -- the rotation angle of `rel` is tiny
    have hQ := abs_le.mp hr.norm
    have hSS : √(s2 rel) * √(s2 rel) = s2 rel := Real.mul_self_sqrt (s2_nonneg rel)
    have hS0 := Real.sqrt_nonneg (s2 rel)
    have hQpos : 0 < val rel.w * val rel.w + √(s2 rel) * √(s2 rel) := by rw [hSS]; linarith
    have hargle := arg_le_sin hr.w_nonneg hS0
    have hz := norm_sum_sq_ge (W := val rel.w) (S := √(s2 rel)) (by rw [hSS]; linarith)
    have hθeq := angle_eq_two_arg hr.w_nonneg hS0 hQpos
    have hθsmall : angleR rel ≤ 2e-149 := by
      rw [hθr, hθeq]
      have hpi := pi_lt_four
      have : √(s2 rel) / √(val rel.w ^ 2 + √(s2 rel) ^ 2) ≤ 4e-150 := by
        rw [div_le_iff₀ (by linarith)]; nlinarith
      nlinarith [arg_range hr.w_nonneg hS0]
    have hθo : val (angleOf rel) ≤ 1.01e-14 := by linarith
    have hzero : ∀ n : Vec, Vec.norm (Vec.sub n n) = 0 := by
      intro n; simp only [Vec.norm, Vec.dot, Vec.sub, sub_self, mul_zero, add_zero,
        Real.sqrt_zero]
    have near : ∀ φ, |φ| ≤ 1.01e-14 → ∀ X : Vec,
        Vec.norm (Vec.sub (rod (Vec.unit ⟨1, 0, 0⟩) φ X) X) ≤ 2.03e-14 * Vec.norm X := by
      intro φ hφ X
      have := rod_sub_le hn1 hn1 φ 0 X
      rw [rod_zero, sub_zero, hzero, add_zero] at this
      have hX := Arc.norm_nonneg X
      calc Vec.norm (Vec.sub (rod (Vec.unit ⟨1, 0, 0⟩) φ X) X) ≤ 2 * |φ| * Vec.norm X := this
        _ ≤ 2.03e-14 * Vec.norm X := by nlinarith
    refine ⟨hn1, fun φ hφ0 hφ => ⟨0, le_refl 0, hθ0, fun X => ?_⟩, fun X => ?_⟩
    · rw [rod_zero]
      have := near φ (by rw [abs_of_nonneg hφ0]; linarith) X
      have hX := Arc.norm_nonneg X
      nlinarith
    · have hX := Arc.norm_nonneg X
      have h1 := near (val (angleOf rel)) (by rw [abs_le]; constructor <;> linarith) X
      have h2 : Vec.norm (Vec.sub X (rod (axisR rel) (angleR rel) X)) ≤ 4e-149 * Vec.norm X := by
        by_cases hS0' : √(s2 rel) = 0
        · have hw : 0 < val rel.w := by
            rw [hS0'] at hQpos; nlinarith [hr.w_nonneg]
          have : angleR rel = 0 := by rw [hθr, hS0']; exact angle_zero hw
          rw [this, rod_zero, hzero]; positivity
        · have hSp : 0 < √(s2 rel) := lt_of_le_of_ne hS0 (Ne.symm hS0')
          have hN : Vec.dot (axisR rel) (axisR rel) = 1 :=
            dot_unit_self (vecPart rel) (by rw [norm_vecPart]; exact hSp)
          have := rod_sub_le hN hN (angleR rel) 0 X
          rw [rod_zero, sub_zero, hzero, add_zero, abs_of_nonneg (show 0 ≤ angleR rel from hθ0),
            norm_sub_swap] at this
          nlinarith
      have h3 := norm_sub_triangle (rod (Vec.unit ⟨1, 0, 0⟩) (val (angleOf rel)) X) X
        (rod (axisR rel) (angleR rel) X)
      nlinarith

/-- An accepted edge from `qa` to `qb`: the commanded rotation by the output angle about the
output axis carries `qa` to within `1e-9` of `qb`, and every attitude within `1e-9` of the
commanded path satisfies every cone. -/
theorem segment_safe {xs : Array Float} {qa qb : Q4} (hqa : GoodQ qa) (hqb : GoodQ qb)
    (hcones : ∀ k : Nat, k < (dims xs).nc.toNat → ConeGood xs (dims xs) (UInt64.ofNat k))
    (hacc : edgeOk xs (dims xs) qa (relative qa qb) = true) :
    (∀ b : Vec, Vec.dot b b = 1 →
      Vec.norm (Vec.sub (rod (Vec.unit (axisOut (relative qa qb))) (val (angleOf (relative qa qb)))
        (attitude (quatOf qa) b)) (attitude (quatOf qb) b)) ≤ 1e-9) ∧
    ∀ φ, 0 ≤ φ → φ ≤ val (angleOf (relative qa qb)) → ∀ R' : Vec → Vec,
      (∀ b : Vec, Vec.dot b b = 1 → Vec.norm (Vec.sub (R' b)
        (rod (Vec.unit (axisOut (relative qa qb))) φ (attitude (quatOf qa) b))) ≤ 1e-9) →
      ∀ k : Nat, k < (dims xs).nc.toNat →
        Holds (!(coneKind xs (dims xs) (UInt64.ofNat k) == 0.0))
          (Vec.unit (vecOf (coneAxis xs (dims xs) (UInt64.ofNat k))))
          (val (coneCos xs (dims xs) (UInt64.ofNat k)))
          (R' (Vec.unit (vecOf (coneBody xs (dims xs) (UInt64.ofNat k))))) := by
  have hr := relative_good hqa hqb
  obtain ⟨_, hH, hE⟩ := segment_close hr
  have hA := qnorm_quatOf_pos hqa
  have hB := qnorm_quatOf_pos hqb
  refine ⟨fun b hb => ?_, fun φ hφ0 hφ R' hR' k hk => ?_⟩
  · have hbn : Vec.norm b = 1 := norm_eq_one_of b hb
    set X := attitude (quatOf qa) b
    have hX : Vec.norm X = 1 := by rw [norm_attitude hA, hbn]
    have h1 := hE X
    rw [hX, mul_one] at h1
    have h2 := relative_rot hqa hqb b
    rw [hbn, mul_one, ← attitude_eq hA, ← attitude_eq hB, ← rod_rel hr] at h2
    have h3 := norm_sub_triangle (rod (Vec.unit (axisOut (relative qa qb)))
      (val (angleOf (relative qa qb))) X) (rod (axisR (relative qa qb))
        (angleR (relative qa qb)) X) (attitude (quatOf qb) b)
    linarith
  · obtain ⟨φ', hφ'0, hφ', hclose⟩ := hH φ hφ0 hφ
    have hsafe := edgeOk_sound hqa hr hcones hacc k hk
    obtain ⟨hgb, _, _, _⟩ := hcones k hk
    have hpos := (norm_near_one _ 3e-12 (by norm_num) hgb.norm).2
    have hbb := dot_unit_self _ hpos
    set bb := Vec.unit (vecOf (coneBody xs (dims xs) (UInt64.ofNat k)))
    set X := attitude (quatOf qa) bb
    have hX : Vec.norm X = 1 := by rw [norm_attitude hA, norm_eq_one_of bb hbb]
    have h1 := hclose X
    rw [hX, mul_one] at h1
    have h2 := hR' bb hbb
    have h3 := norm_sub_triangle (R' bb)
      (rod (Vec.unit (axisOut (relative qa qb))) φ X) (rod (axisR (relative qa qb)) φ' X)
    exact hsafe φ' hφ'0 hφ' (R' bb) (by
      show Vec.norm (Vec.sub (R' bb) (rod (axisR (relative qa qb)) φ' X)) ≤ 1.05e-9
      linarith)

/-! ### The plan -/

theorem segValue_quat (xs : Array Float) (d : Dims) (st a b : UInt64) :
    segValue xs d st a b (UInt64.ofNat 0) = (nodeAt xs d a).w ∧
      segValue xs d st a b (UInt64.ofNat 1) = (nodeAt xs d a).x ∧
      segValue xs d st a b (UInt64.ofNat 2) = (nodeAt xs d a).y ∧
      segValue xs d st a b (UInt64.ofNat 3) = (nodeAt xs d a).z := ⟨rfl, rfl, rfl, rfl⟩

theorem segValue_angle (xs : Array Float) (d : Dims) (st a b : UInt64) :
    segValue xs d st a b (UInt64.ofNat 7) =
      angleOf (relative (nodeAt xs d a) (nodeAt xs d b)) := rfl

theorem segValue_axis (xs : Array Float) (d : Dims) (st a b : UInt64) :
    val (segValue xs d st a b (UInt64.ofNat 4)) =
        (axisOut (relative (nodeAt xs d a) (nodeAt xs d b))).x ∧
      val (segValue xs d st a b (UInt64.ofNat 5)) =
        (axisOut (relative (nodeAt xs d a) (nodeAt xs d b))).y ∧
      val (segValue xs d st a b (UInt64.ofNat 6)) =
        (axisOut (relative (nodeAt xs d a) (nodeAt xs d b))).z := by
  set rel := relative (nodeAt xs d a) (nodeAt xs d b)
  have e4 : segValue xs d st a b (UInt64.ofNat 4) =
      if decide (Demos.Slew.axisMin ≤ sOf rel) = true then rel.x / sOf rel else 1.0 := rfl
  have e5 : segValue xs d st a b (UInt64.ofNat 5) =
      if decide (Demos.Slew.axisMin ≤ sOf rel) = true then rel.y / sOf rel else 0.0 := rfl
  have e6 : segValue xs d st a b (UInt64.ofNat 6) =
      if decide (Demos.Slew.axisMin ≤ sOf rel) = true then rel.z / sOf rel else 0.0 := rfl
  rw [e4, e5, e6]
  by_cases hb : Demos.Slew.axisMin ≤ sOf rel
  · simp only [decide_eq_true_eq, hb, ite_true, axisOut, and_self]
  · simp only [decide_eq_true_eq, hb, ite_false, axisOut, one_val.2, zero_val.2, and_self]

/-- **Safety of the slew planner.**  For an output of status 1 with `K` segments, the plan
starts at the input's start quaternion and ends at its goal quaternion, bit for bit.  Segment `g`
has its start quaternion at offset `4 + 11 g`, its axis at `8 + 11 g`, and its angle at
`11 + 11 g`, and the next start quaternion, or the goal, at `4 + 11 (g + 1)`.  Its rotation by
its angle about its normalized axis carries its normalized start attitude to within `1e-9` of
the next.  For every angle `φ` from 0 to its angle and every map `R'` that moves every unit
vector at most `1e-9` from the attitude after the rotation by `φ`, every cone of the input
holds of `R'` applied to the cone's normalized body vector: a keep-out cone gives a cosine with
the normalized cone axis of at most the cone's cosine, and a keep-in cone at least. -/
theorem plan_safe {xs : Array Float} (h : (plan xs)[0]! = 1.0) :
    ∃ K : Nat, 1 ≤ K ∧ (plan xs).size = 8 + 11 * K ∧
      (∀ i < 4, (plan xs)[4 + i]! = rd xs (8 + UInt64.ofNat i) ∧
        (plan xs)[4 + 11 * K + i]! = rd xs (12 + UInt64.ofNat i)) ∧
      ∀ g < K,
        (∀ b : Vec, Vec.dot b b = 1 → Vec.norm (Vec.sub
          (rod (Vec.unit (vecAt (plan xs) (8 + 11 * g))) (val (plan xs)[11 + 11 * g]!)
            (attitude (quatAt (plan xs) (4 + 11 * g)) b))
          (attitude (quatAt (plan xs) (4 + 11 * (g + 1))) b)) ≤ 1e-9) ∧
        ∀ φ, 0 ≤ φ → φ ≤ val (plan xs)[11 + 11 * g]! → ∀ R' : Vec → Vec,
          (∀ b : Vec, Vec.dot b b = 1 → Vec.norm (Vec.sub (R' b)
            (rod (Vec.unit (vecAt (plan xs) (8 + 11 * g))) φ
              (attitude (quatAt (plan xs) (4 + 11 * g)) b))) ≤ 1e-9) →
          ∀ k : Nat, k < (dims xs).nc.toNat →
            Holds (!(coneKind xs (dims xs) (UInt64.ofNat k) == 0.0))
              (Vec.unit (vecOf (coneAxis xs (dims xs) (UInt64.ofNat k))))
              (val (coneCos xs (dims xs) (UInt64.ofNat k)))
              (R' (Vec.unit (vecOf (coneBody xs (dims xs) (UInt64.ofNat k))))) := by
  have hv0 := (plan_cases h).1
  obtain ⟨hnodes, hcones, hnw⟩ := valid_good hv0
  obtain ⟨_, K, hsz, node, h0, hK, hlt, hacc, hseg, hgoal⟩ := plan_segments h hnw
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with e | e
    · rw [e] at hK; rw [hK] at h0; exact absurd h0 (by decide)
    · exact e
  have hq : ∀ g ≤ K, quatAt (plan xs) (4 + 11 * g) = quatOf (nodeAt xs (dims xs) (node g)) := by
    intro g hg
    rcases lt_or_eq_of_le hg with hg | e
    · obtain ⟨q0, q1, q2, q3⟩ := segValue_quat xs (dims xs) (ceilMs (rd xs 6)) (node g)
        (node (g + 1))
      ext
      · simp only [quatAt, quatOf]
        rw [show 4 + 11 * g = 4 + 11 * g + 0 from rfl, hseg g hg 0 (by norm_num), q0]
      · simp only [quatAt, quatOf]; rw [hseg g hg 1 (by norm_num), q1]
      · simp only [quatAt, quatOf]; rw [hseg g hg 2 (by norm_num), q2]
      · simp only [quatAt, quatOf]; rw [hseg g hg 3 (by norm_num), q3]
    · rw [e, hK]
      have hn1 : nodeAt xs (dims xs) 1 = q4At xs 12 := rfl
      rw [hn1]
      ext
      · simp only [quatAt, quatOf]
        rw [show 4 + 11 * K = 4 + 11 * K + 0 from rfl, (hgoal 0 (by norm_num))]; rfl
      · simp only [quatAt, quatOf]; rw [(hgoal 1 (by norm_num))]; rfl
      · simp only [quatAt, quatOf]; rw [(hgoal 2 (by norm_num))]; rfl
      · simp only [quatAt, quatOf]; rw [(hgoal 3 (by norm_num))]; rfl
  refine ⟨K, hK1, hsz, fun i hi => ⟨?_, hgoal i hi⟩, fun g hg => ?_⟩
  · have hs := hseg 0 hK1 i (by omega)
    rw [show 4 + 11 * 0 + i = 4 + i by ring, h0] at hs
    rw [hs]
    obtain ⟨q0, q1, q2, q3⟩ := segValue_quat xs (dims xs) (ceilMs (rd xs 6)) 0 (node (0 + 1))
    have hn0 : nodeAt xs (dims xs) 0 = q4At xs 8 := rfl
    interval_cases i
    · rw [q0, hn0]; rfl
    · rw [q1, hn0]; rfl
    · rw [q2, hn0]; rfl
    · rw [q3, hn0]; rfl
  · have hqa := hnodes (node g) (hlt g hg.le)
    have hqb := hnodes (node (g + 1)) (hlt (g + 1) hg)
    obtain ⟨hconn, hsafe⟩ := segment_safe hqa hqb hcones (hacc g hg)
    obtain ⟨a4, a5, a6⟩ := segValue_axis xs (dims xs) (ceilMs (rd xs 6)) (node g) (node (g + 1))
    have hax : vecAt (plan xs) (8 + 11 * g) =
        axisOut (relative (nodeAt xs (dims xs) (node g)) (nodeAt xs (dims xs) (node (g + 1)))) := by
      ext
      · simp only [vecAt]
        rw [show 8 + 11 * g = 4 + 11 * g + 4 by ring, hseg g hg 4 (by norm_num), a4]
      · simp only [vecAt]
        rw [show 8 + 11 * g + 1 = 4 + 11 * g + 5 by ring, hseg g hg 5 (by norm_num), a5]
      · simp only [vecAt]
        rw [show 8 + 11 * g + 2 = 4 + 11 * g + 6 by ring, hseg g hg 6 (by norm_num), a6]
    have hang : (plan xs)[11 + 11 * g]! =
        angleOf (relative (nodeAt xs (dims xs) (node g)) (nodeAt xs (dims xs) (node (g + 1)))) := by
      rw [show 11 + 11 * g = 4 + 11 * g + 7 by ring, hseg g hg 7 (by norm_num), segValue_angle]
    rw [hax, hang, hq g hg.le, hq (g + 1) hg]
    exact ⟨hconn, hsafe⟩

end Demos.Slew.Safety
