import Demos.Avoidance.TwoBody

/-!
The encounter plane of the model.  `plane_eq` writes the miss vector and the projected covariance
of `plane` with the axes `axisX`, `axisY`, and `axisZ`.  `axes_orthonormal` (M3) states that for
`|w × ν| > 0` and `|ν| > 0`, `x̂` and `ŷ` are unit vectors perpendicular to each other and to `ν`,
and `miss_closest` (M4) that the miss vector is the point of the straight line `ρ + τ ν` nearest
the origin.  `relative_two_body` (M5) states that the relative state of the model is that of the
two-body trajectory after the burn when the nominal state of the primary is the two-body one.
-/

open Real Demos.Orbit Demos.Orbit.V3

namespace Demos.Avoidance

/-- The unit vector along `w × ν`. -/
noncomputable def axisX (u w : V3) : V3 :=
  ⟨(cross w u).x / V3.norm (cross w u), (cross w u).y / V3.norm (cross w u),
    (cross w u).z / V3.norm (cross w u)⟩

/-- The unit vector along `ν`. -/
noncomputable def axisZ (u : V3) : V3 := ⟨u.x / V3.norm u, u.y / V3.norm u, u.z / V3.norm u⟩

/-- `ẑ × x̂`. -/
noncomputable def axisY (u w : V3) : V3 := cross (axisZ u) (axisX u w)

/-- The symmetric matrix with the entries `xx`, `xy`, `xz`, `yy`, `yz`, and `zz` applied to `e`. -/
def covMul (cxx cxy cxz cyy cyz czz : ℝ) (e : V3) : V3 :=
  ⟨cxx * e.x + cxy * e.y + cxz * e.z, cxy * e.x + cyy * e.y + cyz * e.z,
    cxz * e.x + cyz * e.y + czz * e.z⟩

theorem plane_eq (p u w : V3) (cxx cxy cxz cyy cyz czz : ℝ) :
    plane p.x p.y p.z u.x u.y u.z w.x w.y w.z cxx cxy cxz cyy cyz czz =
      (dot p (axisX u w), dot p (axisY u w),
        dot (axisX u w) (covMul cxx cxy cxz cyy cyz czz (axisX u w)),
        dot (axisX u w) (covMul cxx cxy cxz cyy cyz czz (axisY u w)),
        dot (axisY u w) (covMul cxx cxy cxz cyy cyz czz (axisY u w)),
        dot (cross w u) (cross w u), dot u u) := rfl

theorem dot_unit {a : V3} (h : 0 < dot a a) :
    dot ⟨a.x / V3.norm a, a.y / V3.norm a, a.z / V3.norm a⟩
      ⟨a.x / V3.norm a, a.y / V3.norm a, a.z / V3.norm a⟩ = 1 := by
  have hn : V3.norm a ^ 2 = dot a a := norm_sq a
  have hn0 : V3.norm a ≠ 0 := by
    intro h0
    rw [h0] at hn
    linarith
  simp only [dot] at hn h ⊢
  field_simp
  linarith

/-- Lagrange's identity. -/
theorem dot_cross_cross (a b : V3) :
    dot (cross a b) (cross a b) = dot a a * dot b b - dot a b ^ 2 := by
  simp only [dot, cross_x, cross_y, cross_z]
  ring

/-- **M3.**  The axes `x̂` and `ŷ` are unit vectors perpendicular to each other and to `ν`. -/
theorem axes_orthonormal {u w : V3} (hx : 0 < dot (cross w u) (cross w u)) (hu : 0 < dot u u) :
    dot (axisX u w) (axisX u w) = 1 ∧ dot (axisY u w) (axisY u w) = 1 ∧
      dot (axisX u w) (axisY u w) = 0 ∧ dot (axisX u w) u = 0 ∧ dot (axisY u w) u = 0 := by
  have ex : dot (axisX u w) (axisX u w) = 1 := dot_unit hx
  have ez : dot (axisZ u) (axisZ u) = 1 := dot_unit hu
  have hxz : dot (axisX u w) (axisZ u) = 0 := by
    have h0 : dot (cross w u) u = 0 := by rw [dot_comm]; exact dot_cross_self' w u
    have e : dot (axisX u w) (axisZ u) =
        dot (cross w u) u / (V3.norm (cross w u) * V3.norm u) := by
      simp only [axisX, axisZ, dot]
      ring
    rw [e, h0, zero_div]
  have hxu : dot (axisX u w) u = 0 := by
    have h0 : dot (cross w u) u = 0 := by rw [dot_comm]; exact dot_cross_self' w u
    have e : dot (axisX u w) u = dot (cross w u) u / V3.norm (cross w u) := by
      simp only [axisX, dot]
      ring
    rw [e, h0, zero_div]
  have hzu : u = V3.norm u • axisZ u := by
    have hn0 : V3.norm u ≠ 0 := by
      intro h0
      have := norm_sq u
      rw [h0] at this
      linarith
    ext <;> simp only [axisZ, smul_x, smul_y, smul_z] <;> field_simp
  refine ⟨ex, ?_, ?_, hxu, ?_⟩
  · unfold axisY
    rw [dot_cross_cross, ez, ex, dot_comm, hxz]
    ring
  · unfold axisY
    exact dot_cross_self' (axisZ u) (axisX u w)
  · unfold axisY
    have h1 : dot (cross (axisZ u) (axisX u w)) u =
        dot (cross (axisZ u) (axisX u w)) (V3.norm u • axisZ u) := by rw [← hzu]
    rw [h1, dot_smul, dot_comm, dot_cross_self, mul_zero]

/-- The squared length of a vector in the frame `x̂`, `ẑ × x̂`, `ẑ` of two orthonormal vectors. -/
theorem parseval {e k v : V3} (he : dot e e = 1) (hk : dot k k = 1) (hek : dot e k = 0) :
    dot v v = dot v e ^ 2 + dot v (cross k e) ^ 2 + dot v k ^ 2 := by
  have g : dot v (cross k e) ^ 2 =
      dot v v * dot k k * dot e e + 2 * dot v k * dot k e * dot e v - dot v v * dot k e ^ 2 -
        dot k k * dot e v ^ 2 - dot e e * dot v k ^ 2 := by
    simp only [dot, cross_x, cross_y, cross_z]
    ring
  rw [dot_comm k e, hek, he, hk, dot_comm e v] at g
  linear_combination -g

/-- **M4.**  For `|w × ν| > 0` and `|ν| > 0`, the miss vector `(ρ · x̂, ρ · ŷ)` is the point of
the line `ρ + τ ν` nearest the origin: its squared length is at most `|ρ + τ ν|²` for every `τ`,
with equality at `τ = -(ρ · ν)/(ν · ν)`. -/
theorem miss_closest {p u w : V3} (hx : 0 < dot (cross w u) (cross w u)) (hu : 0 < dot u u) :
    (∀ τ : ℝ, dot p (axisX u w) ^ 2 + dot p (axisY u w) ^ 2 ≤ dot (p + τ • u) (p + τ • u)) ∧
      dot p (axisX u w) ^ 2 + dot p (axisY u w) ^ 2 =
        dot (p + (-(dot p u) / dot u u) • u) (p + (-(dot p u) / dot u u) • u) := by
  obtain ⟨ex, -, -, hxu, hyu⟩ := axes_orthonormal hx hu
  have ez : dot (axisZ u) (axisZ u) = 1 := dot_unit hu
  have hxz : dot (axisX u w) (axisZ u) = 0 := by
    have h0 : dot (cross w u) u = 0 := by rw [dot_comm]; exact dot_cross_self' w u
    have e : dot (axisX u w) (axisZ u) =
        dot (cross w u) u / (V3.norm (cross w u) * V3.norm u) := by
      simp only [axisX, axisZ, dot]
      ring
    rw [e, h0, zero_div]
  have key : ∀ τ : ℝ, dot (p + τ • u) (p + τ • u) =
      dot p (axisX u w) ^ 2 + dot p (axisY u w) ^ 2 + dot (p + τ • u) (axisZ u) ^ 2 := by
    intro τ
    have h := parseval (v := p + τ • u) ex ez hxz
    have e1 : dot (p + τ • u) (axisX u w) = dot p (axisX u w) := by
      rw [dot_comm, dot_add, dot_smul, hxu, mul_zero, add_zero, dot_comm]
    have e2 : dot (p + τ • u) (cross (axisZ u) (axisX u w)) = dot p (axisY u w) := by
      unfold axisY at hyu ⊢
      rw [dot_comm, dot_add, dot_smul, hyu, mul_zero, add_zero, dot_comm]
    rw [e1, e2] at h
    exact h
  refine ⟨fun τ => by rw [key τ]; nlinarith [sq_nonneg (dot (p + τ • u) (axisZ u))], ?_⟩
  rw [key]
  have hn0 : V3.norm u ≠ 0 := by
    intro h0
    have := norm_sq u
    rw [h0] at this
    linarith
  have hz : dot (p + (-(dot p u) / dot u u) • u) (axisZ u) = 0 := by
    have e : dot (p + (-(dot p u) / dot u u) • u) (axisZ u) =
        (dot p u + -(dot p u) / dot u u * dot u u) / V3.norm u := by
      simp only [dot, axisZ, add_x, add_y, add_z, smul_x, smul_y, smul_z]
      ring
    rw [e, div_mul_cancel₀ _ hu.ne', add_neg_cancel, zero_div]
  rw [hz]
  ring

/-- **M5.**  When the nominal state of the primary at the reference time is the two-body
propagation of its state at the burn, the model's relative state after the burn `dv` with the
displacement `d` is the two-body state after the burn, less the secondary's state, plus `d`. -/
theorem relative_two_body (mu dt : ℝ) (rb vb dv r2 v2 d : V3) :
    relative mu rb.x rb.y rb.z vb.x vb.y vb.z dv.x dv.y dv.z dt
        (stateAt mu rb vb dt).1.x (stateAt mu rb vb dt).1.y (stateAt mu rb vb dt).1.z
        (stateAt mu rb vb dt).2.x (stateAt mu rb vb dt).2.y (stateAt mu rb vb dt).2.z
        r2.x r2.y r2.z v2.x v2.y v2.z d.x d.y d.z =
      (((stateAt mu rb (vb + dv) dt).1 - r2 + d).x, ((stateAt mu rb (vb + dv) dt).1 - r2 + d).y,
        ((stateAt mu rb (vb + dv) dt).1 - r2 + d).z, ((stateAt mu rb (vb + dv) dt).2 - v2).x,
        ((stateAt mu rb (vb + dv) dt).2 - v2).y, ((stateAt mu rb (vb + dv) dt).2 - v2).z) := by
  simp only [relative, stateAt, add_x, add_y, add_z, sub_x, sub_y, sub_z, Prod.mk.injEq]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring⟩

/-- The centered form of `project` is the plain projection: its value does not depend on the
centers `g` and `h`. -/
theorem project_eq (px py pz ex ey ez fx fy fz gx gy gz hx hy hz cxx cxy cxz cyy cyz czz : ℝ) :
    project px py pz ex ey ez fx fy fz gx gy gz hx hy hz cxx cxy cxz cyy cyz czz =
      (px * ex + py * ey + pz * ez, px * fx + py * fy + pz * fz,
        ex * (cxx * ex + cxy * ey + cxz * ez) + ey * (cxy * ex + cyy * ey + cyz * ez) +
          ez * (cxz * ex + cyz * ey + czz * ez),
        ex * (cxx * fx + cxy * fy + cxz * fz) + ey * (cxy * fx + cyy * fy + cyz * fz) +
          ez * (cxz * fx + cyz * fy + czz * fz),
        fx * (cxx * fx + cxy * fy + cxz * fz) + fy * (cxy * fx + cyy * fy + cyz * fz) +
          fz * (cxz * fx + cyz * fy + czz * fz)) := by
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))) <;> simp only [project] <;>
    ring

#print axioms axes_orthonormal
#print axioms miss_closest
#print axioms relative_two_body

end Demos.Avoidance
