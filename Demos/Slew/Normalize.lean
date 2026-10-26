import Demos.Slew.Arc

/-! The normalization of the inputs.  The specification states the cones for the normalized
axis `ū`, body vector `b̄`, and attitude `q̄`, while the program computes with the inputs as given,
whose squared norms lie within `3e-12` of 1.  `spec_close` bounds the difference between the two
cosines along a rotation about a unit axis by `1.3e-11`.  The other lemmas bound components,
cross products, and the rotation formula's lengths for such inputs. -/

namespace Demos.Slew.Normalize

open Demos.Slew.Spec Demos.Slew.Arc Vec

/-! ### Lengths -/

theorem norm_sq (a : Vec) : norm a * norm a = dot a a := Real.mul_self_sqrt (dot_self_nonneg a)

theorem norm_eq_one_of (a : Vec) (h : dot a a = 1) : norm a = 1 := by rw [Vec.norm, h, Real.sqrt_one]

/-- A vector whose squared norm is within `ε ≤ 1/2` of 1 has norm within `ε` of 1. -/
theorem norm_near_one (a : Vec) (ε : ℝ) (hε : ε ≤ 1 / 2) (h : |dot a a - 1| ≤ ε) :
    |norm a - 1| ≤ ε ∧ 0 < norm a := by
  have hn := norm_sq a
  have h0 := norm_nonneg a
  have hab := abs_le.mp h
  have hpos : 0 < norm a := by nlinarith
  refine ⟨?_, hpos⟩
  rw [abs_le]
  constructor <;> nlinarith

theorem abs_component_le (a : Vec) : |a.x| ≤ norm a ∧ |a.y| ≤ norm a ∧ |a.z| ≤ norm a := by
  refine ⟨Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_⟩ <;> simp only [dot, sq] <;>
    nlinarith [mul_self_nonneg a.x, mul_self_nonneg a.y, mul_self_nonneg a.z]

theorem dot_add_sub (a b : Vec) :
    dot (sub a b) (sub a b) = dot a a - 2 * dot a b + dot b b := by
  simp only [dot, sub]; ring

/-- The triangle inequality for a difference. -/
theorem norm_sub_le (a b : Vec) : norm (sub a b) ≤ norm a + norm b := by
  have h := abs_dot_le a b
  have ha := norm_sq a
  have hb := norm_sq b
  rw [Vec.norm, dot_add_sub]
  rw [show norm a + norm b = √((norm a + norm b) ^ 2) by
    rw [Real.sqrt_sq (add_nonneg (norm_nonneg a) (norm_nonneg b))]]
  apply Real.sqrt_le_sqrt
  nlinarith [abs_le.mp h, norm_nonneg a, norm_nonneg b]

theorem sub_sub_sub (a b c : Vec) : sub a c = sub (sub a b) (sub c b) := by
  ext <;> simp only [sub] <;> ring

theorem norm_sub_triangle (a b c : Vec) : norm (sub a c) ≤ norm (sub a b) + norm (sub b c) := by
  have h := norm_sub_le (sub a b) (sub c b)
  rw [← sub_sub_sub] at h
  have e : norm (sub c b) = norm (sub b c) := by
    rw [Vec.norm, Vec.norm]; congr 1; simp only [dot, sub]; ring
  linarith

theorem dot_cross_self (a b : Vec) :
    dot (cross a b) (cross a b) = dot a a * dot b b - dot a b ^ 2 := by
  simp only [dot, cross]; ring

theorem norm_cross_le (a b : Vec) : norm (cross a b) ≤ norm a * norm b := by
  rw [Vec.norm, Vec.norm, Vec.norm, ← Real.sqrt_mul (dot_self_nonneg a), dot_cross_self]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (dot a b)])

/-- The rotation formula's length for any quaternion. -/
theorem dot_rot_general (q : Quat) (v : Vec) :
    dot (Quat.rot q v) (Quat.rot q v) = dot v v + 4 * (Quat.norm2 q - 1) *
      ((q.x * q.x + q.y * q.y + q.z * q.z) * dot v v - (q.x * v.x + q.y * v.y + q.z * v.z) ^ 2) := by
  simp only [dot, Quat.rot, Quat.norm2]
  ring

/-- For near-unit `q` and `v`, the rotation formula's result has norm at most `1.0001`. -/
theorem norm_rot_le (q : Quat) (v : Vec) (hq : |Quat.norm2 q - 1| ≤ 3e-12)
    (hv : |dot v v - 1| ≤ 3e-12) : norm (Quat.rot q v) ≤ 1.0001 := by
  have e := dot_rot_general q v
  have hq' := abs_le.mp hq
  have hv' := abs_le.mp hv
  have hA : 0 ≤ (q.x * q.x + q.y * q.y + q.z * q.z) * dot v v - (q.x * v.x + q.y * v.y + q.z * v.z) ^ 2 := by
    have := dot_sq_le ⟨q.x, q.y, q.z⟩ v
    simp only [dot] at this ⊢; nlinarith
  have hA' : (q.x * q.x + q.y * q.y + q.z * q.z) * dot v v - (q.x * v.x + q.y * v.y + q.z * v.z) ^ 2 ≤ 2 := by
    have hn : q.x * q.x + q.y * q.y + q.z * q.z ≤ Quat.norm2 q := by
      simp only [Quat.norm2]; nlinarith [mul_self_nonneg q.w]
    nlinarith [sq_nonneg (q.x * v.x + q.y * v.y + q.z * v.z), dot_self_nonneg v]
  rw [Vec.norm, show (1.0001 : ℝ) = √(1.0001 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  apply Real.sqrt_le_sqrt
  rw [e]
  nlinarith

/-! ### The normalized cosine -/

theorem unit_sub (a : Vec) : sub (unit a) a = smul (1 / norm a - 1) a := by
  ext <;> simp only [unit, sub, smul] <;> ring

theorem norm_unit_sub (a : Vec) (h : 0 < norm a) : norm (sub (unit a) a) = |1 - norm a| := by
  rw [unit_sub, norm_smul]
  rw [show 1 / norm a - 1 = (1 - norm a) / norm a by field_simp, abs_div, abs_of_pos h]
  field_simp

theorem quat_unit_smul (q : Quat) (h : 0 < Quat.norm2 q) :
    Quat.smul (√(Quat.norm2 q)) (Quat.unit q) = q := by
  have hs : √(Quat.norm2 q) ≠ 0 := (Real.sqrt_pos.mpr h).ne'
  ext <;> simp only [Quat.smul, Quat.unit] <;> field_simp

theorem norm2_unit (q : Quat) (h : 0 < Quat.norm2 q) : Quat.norm2 (Quat.unit q) = 1 := by
  have e : Quat.norm2 (Quat.unit q) = (1 / √(Quat.norm2 q)) ^ 2 * Quat.norm2 q := by
    simp only [Quat.norm2, Quat.unit, Quat.smul]; ring
  rw [e, div_pow, one_pow, Real.sq_sqrt h.le, one_div_mul_cancel h.ne']

/-- The rotation formula on the given and on the normalized inputs. -/
theorem rot_close (q : Quat) (v : Vec) (hq : |Quat.norm2 q - 1| ≤ 3e-12)
    (hv : |dot v v - 1| ≤ 3e-12) :
    norm (sub (Quat.rot (Quat.unit q) (unit v)) (Quat.rot q v)) ≤ 9.1e-12 := by
  have hq' := abs_le.mp hq
  have hqpos : 0 < Quat.norm2 q := by linarith
  obtain ⟨hvn, hvpos⟩ := norm_near_one v 3e-12 (by norm_num) hv
  set qb := Quat.unit q
  have hqb := norm2_unit q hqpos
  set lam := √(Quat.norm2 q)
  have hlam : lam * lam = Quat.norm2 q := Real.mul_self_sqrt hqpos.le
  -- rot q v = v + lam² (rot qb v - v)
  have hsmul := rot_smul_left qb lam v
  rw [quat_unit_smul q hqpos] at hsmul
  -- the two parts
  have p1 : norm (sub (Quat.rot qb (unit v)) (Quat.rot qb v)) = |1 - norm v| := by
    rw [← rot_sub, Vec.norm, dot_rot_self qb _ hqb, ← Vec.norm, norm_unit_sub v hvpos]
  have p2 : norm (sub (Quat.rot qb v) (Quat.rot q v)) ≤ |lam * lam - 1| * (2 * norm v) := by
    have e : sub (Quat.rot qb v) (Quat.rot q v) = smul (1 - lam * lam) (sub (Quat.rot qb v) v) := by
      have hx := congrArg Vec.x hsmul
      have hy := congrArg Vec.y hsmul
      have hz := congrArg Vec.z hsmul
      simp only [sub, smul] at hx hy hz
      ext <;> simp only [sub, smul] <;> linarith
    rw [e, norm_smul, abs_sub_comm]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h1 := norm_sub_le (Quat.rot qb v) v
    have h2 : norm (Quat.rot qb v) = norm v := by rw [Vec.norm, Vec.norm, dot_rot_self qb v hqb]
    linarith
  have t := norm_sub_triangle (Quat.rot qb (unit v)) (Quat.rot qb v) (Quat.rot q v)
  rw [p1] at t
  rw [hlam] at p2
  have hv1 : norm v ≤ 1 + 3e-12 := by linarith [abs_le.mp hvn]
  have hvn' := abs_le.mp hvn
  calc norm (sub (Quat.rot qb (unit v)) (Quat.rot q v))
      ≤ |1 - norm v| + |Quat.norm2 q - 1| * (2 * norm v) := t.trans (add_le_add le_rfl p2)
    _ ≤ 3e-12 + 3e-12 * (2 * (1 + 3e-12)) := by
        apply add_le_add
        · rw [abs_sub_comm]; exact hvn
        · exact mul_le_mul hq (by linarith) (by positivity) (by norm_num)
    _ ≤ 9.1e-12 := by norm_num

/-- The cosine of the normalized inputs along a rotation about a unit axis lies within `1.3e-11`
of the cosine of the given inputs. -/
theorem spec_close (U B : Vec) (Q : Quat) (N : Vec) (φ : ℝ) (hN : dot N N = 1)
    (hU : |dot U U - 1| ≤ 3e-12) (hB : |dot B B - 1| ≤ 3e-12) (hQ : |Quat.norm2 Q - 1| ≤ 3e-12) :
    |dot (unit U) (rod N φ (Quat.rot (Quat.unit Q) (unit B))) - dot U (rod N φ (Quat.rot Q B))| ≤
      1.3e-11 := by
  obtain ⟨hUn, hUpos⟩ := norm_near_one U 3e-12 (by norm_num) hU
  set P := Quat.rot (Quat.unit Q) (unit B)
  set V := Quat.rot Q B
  have hV := norm_rot_le Q B hQ hB
  have hPV := rot_close Q B hQ hB
  have e : dot (unit U) (rod N φ P) - dot U (rod N φ V) =
      dot (unit U) (rod N φ (sub P V)) + dot (sub (unit U) U) (rod N φ V) := by
    rw [rod_sub]; simp only [dot, sub]; ring
  rw [e]
  have h1 : |dot (unit U) (rod N φ (sub P V))| ≤ norm (sub P V) := by
    have := abs_dot_le (unit U) (rod N φ (sub P V))
    rw [norm_unit U hUpos, one_mul] at this
    rwa [show norm (rod N φ (sub P V)) = norm (sub P V) by
      rw [Vec.norm, Vec.norm, dot_rod_self N φ _ hN]] at this
  have h2 : |dot (sub (unit U) U) (rod N φ V)| ≤ |1 - norm U| * norm V := by
    have := abs_dot_le (sub (unit U) U) (rod N φ V)
    rw [norm_unit_sub U hUpos] at this
    rwa [show norm (rod N φ V) = norm V by rw [Vec.norm, Vec.norm, dot_rod_self N φ V hN]] at this
  calc |dot (unit U) (rod N φ (sub P V)) + dot (sub (unit U) U) (rod N φ V)|
      ≤ |dot (unit U) (rod N φ (sub P V))| + |dot (sub (unit U) U) (rod N φ V)| := abs_add_le _ _
    _ ≤ 9.1e-12 + 3e-12 * 1.0001 := by
        apply add_le_add (h1.trans hPV)
        exact h2.trans (mul_le_mul (by rw [abs_sub_comm]; exact hUn) hV (norm_nonneg _) (by norm_num))
    _ ≤ 1.3e-11 := by norm_num

end Demos.Slew.Normalize
