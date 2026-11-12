import Demos.Attitude.Bound

/-! Matrices near TRIAD's attitude.  `Mat` is a 3×3 matrix of reals in rows, `triadMat` is TRIAD's
attitude as a matrix, and `Near M T w` states that each entry of `M` lies within the matching
entry of `w` of the entry of `T`.  `vangle_near` bounds the angle between `M v` and `T v` for a
unit `v` and a rotation `T` by `arcsin (η / (1 - η))`, where `η` is the root of the sum of the
squared entries of `w`. -/

namespace Demos.Attitude

open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Normalize Demos.Slew.Premise Vec Real

/-- A 3×3 matrix of reals, row by row. -/
structure Mat where
  m11 : ℝ
  m12 : ℝ
  m13 : ℝ
  m21 : ℝ
  m22 : ℝ
  m23 : ℝ
  m31 : ℝ
  m32 : ℝ
  m33 : ℝ

def Mat.apply (M : Mat) (v : Vec) : Vec :=
  ⟨M.m11 * v.x + M.m12 * v.y + M.m13 * v.z, M.m21 * v.x + M.m22 * v.y + M.m23 * v.z,
    M.m31 * v.x + M.m32 * v.y + M.m33 * v.z⟩

/-- The matrix of the map between two frames: entry `jk` is `Σ_i (s_i)_j (t_i)_k`. -/
def Frame.mat (t s : Frame) : Mat :=
  ⟨s.e1.x * t.e1.x + s.e2.x * t.e2.x + s.e3.x * t.e3.x, s.e1.x * t.e1.y + s.e2.x * t.e2.y + s.e3.x * t.e3.y,
    s.e1.x * t.e1.z + s.e2.x * t.e2.z + s.e3.x * t.e3.z, s.e1.y * t.e1.x + s.e2.y * t.e2.x + s.e3.y * t.e3.x,
    s.e1.y * t.e1.y + s.e2.y * t.e2.y + s.e3.y * t.e3.y, s.e1.y * t.e1.z + s.e2.y * t.e2.z + s.e3.y * t.e3.z,
    s.e1.z * t.e1.x + s.e2.z * t.e2.x + s.e3.z * t.e3.x, s.e1.z * t.e1.y + s.e2.z * t.e2.y + s.e3.z * t.e3.y,
    s.e1.z * t.e1.z + s.e2.z * t.e2.z + s.e3.z * t.e3.z⟩

/-- TRIAD's attitude as a matrix. -/
noncomputable def triadMat (b1 b2 r1 r2 : Vec) : Mat := Frame.mat (frame b1 b2) (frame r1 r2)

theorem mat_apply (t s : Frame) (v : Vec) : (Frame.mat t s).apply v = Frame.map t s v := by
  ext <;> simp only [Mat.apply, Frame.mat, Frame.map, comb, dot] <;> ring

theorem triadMat_apply (b1 b2 r1 r2 v : Vec) : (triadMat b1 b2 r1 r2).apply v = triadMap b1 b2 r1 r2 v :=
  mat_apply _ _ v

/-- Each entry of `M` lies within the matching entry of `w` of the entry of `T`. -/
def Near (M T w : Mat) : Prop :=
  |M.m11 - T.m11| ≤ w.m11 ∧ |M.m12 - T.m12| ≤ w.m12 ∧ |M.m13 - T.m13| ≤ w.m13 ∧
  |M.m21 - T.m21| ≤ w.m21 ∧ |M.m22 - T.m22| ≤ w.m22 ∧ |M.m23 - T.m23| ≤ w.m23 ∧
  |M.m31 - T.m31| ≤ w.m31 ∧ |M.m32 - T.m32| ≤ w.m32 ∧ |M.m33 - T.m33| ≤ w.m33

/-- The sum of the squared entries. -/
def Mat.sumSq (w : Mat) : ℝ :=
  w.m11 * w.m11 + w.m12 * w.m12 + w.m13 * w.m13 + w.m21 * w.m21 + w.m22 * w.m22 +
    w.m23 * w.m23 + w.m31 * w.m31 + w.m32 * w.m32 + w.m33 * w.m33

/-- One row: `(Σ d_k v_k)² ≤ Σ w_k²` for `|d_k| ≤ w_k` and a unit `v`. -/
theorem row_sq_le {d1 d2 d3 w1 w2 w3 : ℝ} (h1 : |d1| ≤ w1) (h2 : |d2| ≤ w2) (h3 : |d3| ≤ w3)
    {v : Vec} (hv : dot v v = 1) :
    (d1 * v.x + d2 * v.y + d3 * v.z) ^ 2 ≤ w1 * w1 + w2 * w2 + w3 * w3 := by
  have cs := dot_sq_le ⟨d1, d2, d3⟩ v
  simp only [dot] at cs hv
  rw [hv, mul_one] at cs
  have e1 : d1 * d1 ≤ w1 * w1 := by
    have := abs_nonneg d1; nlinarith [abs_mul_abs_self d1]
  have e2 : d2 * d2 ≤ w2 * w2 := by
    have := abs_nonneg d2; nlinarith [abs_mul_abs_self d2]
  have e3 : d3 * d3 ≤ w3 * w3 := by
    have := abs_nonneg d3; nlinarith [abs_mul_abs_self d3]
  linarith

theorem near_dist {M T w : Mat} (h : Near M T w) {v : Vec} (hv : dot v v = 1) :
    dot (sub (M.apply v) (T.apply v)) (sub (M.apply v) (T.apply v)) ≤ w.sumSq := by
  obtain ⟨h11, h12, h13, h21, h22, h23, h31, h32, h33⟩ := h
  have r1 := row_sq_le h11 h12 h13 hv
  have r2 := row_sq_le h21 h22 h23 hv
  have r3 := row_sq_le h31 h32 h33 hv
  have e : dot (sub (M.apply v) (T.apply v)) (sub (M.apply v) (T.apply v)) =
      ((M.m11 - T.m11) * v.x + (M.m12 - T.m12) * v.y + (M.m13 - T.m13) * v.z) ^ 2 +
      ((M.m21 - T.m21) * v.x + (M.m22 - T.m22) * v.y + (M.m23 - T.m23) * v.z) ^ 2 +
      ((M.m31 - T.m31) * v.x + (M.m32 - T.m32) * v.y + (M.m33 - T.m33) * v.z) ^ 2 := by
    simp only [dot, sub, Mat.apply]; ring
  rw [e, Mat.sumSq]
  linarith

/-- The angle between `w` and a unit vector `a` within `η ≤ 1/4` of it is at most
`arcsin (η / (1 - η))`. -/
theorem vangle_near {w a : Vec} (ha : dot a a = 1) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 4)
    (h : dot (sub w a) (sub w a) ≤ η ^ 2) : vangle w a ≤ arcsin (η / (1 - η)) := by
  have hpi := pi_pos
  set e := sub w a
  have hwa : w = ⟨a.x + e.x, a.y + e.y, a.z + e.z⟩ := by
    ext <;> simp only [e, sub] <;> ring
  -- the cross product, the dot product, and the length of w
  have hcross : dot (cross w a) (cross w a) ≤ η ^ 2 := by
    have e1 : cross w a = cross e a := by
      rw [hwa]; ext <;> simp only [cross, e, sub] <;> ring
    rw [e1, dot_cross_self, ha, mul_one]
    nlinarith [sq_nonneg (dot e a)]
  have hea : |dot e a| ≤ η := by
    have := abs_dot_le e a
    rw [norm_one_of ha, mul_one] at this
    have hn : norm e ≤ η := by
      rw [Vec.norm]
      calc √(dot e e) ≤ √(η ^ 2) := Real.sqrt_le_sqrt h
        _ = η := Real.sqrt_sq hη0
    linarith
  have hdot : 1 - η ≤ dot w a := by
    have e2 : dot w a = 1 + dot e a := by
      rw [hwa]; simp only [dot] at ha ⊢; linarith
    rw [e2]; linarith [(abs_le.mp hea).1]
  have hww : dot w w = dot (cross w a) (cross w a) + dot w a ^ 2 := by
    rw [dot_cross_self, ha]; ring
  have hwpos : (1 - η) ^ 2 ≤ dot w w := by
    rw [hww]; nlinarith [dot_self_nonneg (cross w a)]
  have hnw : 0 < norm w := by
    rw [Vec.norm]; apply Real.sqrt_pos.mpr; nlinarith
  -- the angle through its cosine
  set k := η / (1 - η)
  have hk0 : 0 ≤ k := div_nonneg hη0 (by linarith)
  have hk1 : k ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hβ0 : 0 ≤ arcsin k := arcsin_nonneg.mpr hk0
  have hβ1 : arcsin k ≤ π / 2 := arcsin_le_pi_div_two _
  rw [vangle, InnerProductGeometry.angle, inner_toE, norm_toE, norm_toE, norm_one_of ha, mul_one]
  calc arccos (dot w a / norm w) ≤ arccos (cos (arcsin k)) := by
        apply arccos_le_arccos
        rw [cos_arcsin, le_div_iff₀ hnw]
        have hc : 0 ≤ √(1 - k ^ 2) := Real.sqrt_nonneg _
        have hsq : (√(1 - k ^ 2) * norm w) ^ 2 ≤ dot w a ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by nlinarith), sq (norm w), norm_sq, hww]
          have : dot (cross w a) (cross w a) ≤ k ^ 2 * dot w w := by
            have hk : η ^ 2 ≤ k ^ 2 * (1 - η) ^ 2 := by
              have h1η : (1 - η) ≠ 0 := by linarith
              have : k ^ 2 * (1 - η) ^ 2 = η ^ 2 := by
                simp only [k]; rw [div_pow]; field_simp
              rw [this]
            nlinarith
          nlinarith [this]
        exact abs_le_of_sq_le_sq' hsq (by linarith) |>.2
    _ = arcsin k := arccos_cos hβ0 (by linarith)

end Demos.Attitude
