import Demos.Slew.Premise

/-! TRIAD over the real numbers.  `frame a b` is the triad `(ā, n, ā × n)` with `n` the unit normal
of `a` and `b`, and `triadMap b1 b2 r1 r2` is the map that sends the frame of the measurements
`b1`, `b2` to the frame of the references `r1`, `r2`, the attitude that maps body coordinates to
inertial coordinates.  `triad_first` and `triad_second` state that it maps `b̄1` to `r̄1` and
`b̄2` into the plane of `r̄1` and `r̄2` on the side of `r̄2`, and `triad_dot` and `triad_cross`
that it preserves dot and cross products, so it is a rotation.  Vectors, quaternions, and the
rotation `act` come from the slew planner. -/

namespace Demos.Attitude

open Demos.Slew.Spec Demos.Slew.Arc Demos.Slew.Normalize Demos.Slew.Rotation Vec

/-- `a1 s1 + a2 s2 + a3 s3`. -/
def comb (a1 a2 a3 : ℝ) (s1 s2 s3 : Vec) : Vec :=
  ⟨a1 * s1.x + a2 * s2.x + a3 * s3.x, a1 * s1.y + a2 * s2.y + a3 * s3.y,
    a1 * s1.z + a2 * s2.z + a3 * s3.z⟩

/-- Three vectors: the columns of a frame. -/
structure Frame where
  e1 : Vec
  e2 : Vec
  e3 : Vec

/-- TRIAD's frame of `a` and `b`: `ā`, the unit normal `n` of `a` and `b`, and `ā × n`. -/
noncomputable def frame (a b : Vec) : Frame :=
  ⟨unit a, unit (cross a b), cross (unit a) (unit (cross a b))⟩

/-- The linear map that sends `t.e_i` to `s.e_i` when `t` is orthonormal. -/
def Frame.map (t s : Frame) (v : Vec) : Vec :=
  comb (dot t.e1 v) (dot t.e2 v) (dot t.e3 v) s.e1 s.e2 s.e3

/-- TRIAD's attitude for the measurements `b1`, `b2` and the references `r1`, `r2`. -/
noncomputable def triadMap (b1 b2 r1 r2 : Vec) (v : Vec) : Vec :=
  Frame.map (frame b1 b2) (frame r1 r2) v

/-- An orthonormal frame whose third vector is the cross product of the first two. -/
structure Frame.Good (t : Frame) : Prop where
  n1 : dot t.e1 t.e1 = 1
  n2 : dot t.e2 t.e2 = 1
  o12 : dot t.e1 t.e2 = 0
  e3 : t.e3 = cross t.e1 t.e2

/-! ### Vector algebra -/

theorem dot_cross_left (a b : Vec) : dot a (cross a b) = 0 := by simp only [dot, cross]; ring

theorem dot_cross_right (a b : Vec) : dot b (cross a b) = 0 := by simp only [dot, cross]; ring

/-- The Binet–Cauchy identity. -/
theorem dot_cross_cross (a b c d : Vec) :
    dot (cross a b) (cross c d) = dot a c * dot b d - dot a d * dot b c := by
  simp only [dot, cross]; ring

theorem cross_smul_left (k : ℝ) (a b : Vec) : cross (smul k a) b = smul k (cross a b) := by
  ext <;> simp only [cross, smul] <;> ring

theorem cross_smul_right (k : ℝ) (a b : Vec) : cross a (smul k b) = smul k (cross a b) := by
  ext <;> simp only [cross, smul] <;> ring

theorem dot_smul_right (k : ℝ) (a b : Vec) : dot a (smul k b) = k * dot a b := by
  simp only [dot, smul]; ring

theorem smul_smul (j k : ℝ) (a : Vec) : smul j (smul k a) = smul (j * k) a := by
  ext <;> simp only [smul] <;> ring

theorem smul_one (a : Vec) : smul 1 a = a := by ext <;> simp only [smul] <;> ring

theorem dot_unit_self {a : Vec} (h : 0 < norm a) : dot (unit a) (unit a) = 1 := by
  rw [← norm_sq, norm_unit a h, one_mul]

theorem unit_smul {k : ℝ} (hk : 0 < k) (a : Vec) : unit (smul k a) = unit a := by
  rw [unit, unit, norm_smul, abs_of_pos hk, smul_smul]
  by_cases ha : norm a = 0
  · rw [ha]; simp
  · congr 1; field_simp

theorem unit_of_dot_one {a : Vec} (h : dot a a = 1) : unit a = a := by
  rw [unit, norm_eq_one_of a h, div_one, smul_one]

theorem norm_pos_of_dot {a : Vec} (h : 0 < dot a a) : 0 < norm a := Real.sqrt_pos.mpr h

theorem dot_pos_of_norm {a : Vec} (h : 0 < norm a) : 0 < dot a a := by
  rw [← norm_sq]; positivity

/-- The cross product of the unit vectors is the cross product scaled by both lengths. -/
theorem cross_unit_unit (a b : Vec) :
    cross (unit a) (unit b) = smul (1 / norm a * (1 / norm b)) (cross a b) := by
  rw [unit, unit, cross_smul_left, cross_smul_right, smul_smul]

theorem unit_cross_unit {a b : Vec} (ha : 0 < norm a) (hb : 0 < norm b) :
    unit (cross (unit a) (unit b)) = unit (cross a b) := by
  rw [cross_unit_unit]; exact unit_smul (by positivity) _

/-! ### Frames -/

theorem frame_good {a b : Vec} (ha : 0 < norm a) (hc : 0 < norm (cross a b)) : (frame a b).Good where
  n1 := dot_unit_self ha
  n2 := dot_unit_self hc
  o12 := by
    show dot (unit a) (unit (cross a b)) = 0
    rw [unit, unit, dot_smul_left, dot_smul_right, dot_cross_left]; ring
  e3 := rfl

namespace Frame.Good

variable {t : Frame} (g : t.Good)
include g

theorem o13 : dot t.e1 t.e3 = 0 := by rw [g.e3, dot_cross_left]

theorem o23 : dot t.e2 t.e3 = 0 := by rw [g.e3, dot_cross_right]

theorem n3 : dot t.e3 t.e3 = 1 := by
  rw [g.e3, dot_cross_self, g.n1, g.n2, g.o12]; ring

/-- Every vector is the combination of a good frame with its dot products. -/
theorem expand (v : Vec) : comb (dot t.e1 v) (dot t.e2 v) (dot t.e3 v) t.e1 t.e2 t.e3 = v := by
  have h1 := g.n1
  have h2 := g.n2
  have h3 := g.o12
  rw [g.e3]
  set a := t.e1
  set b := t.e2
  simp only [dot] at h1 h2 h3
  ext
  · simp only [comb, dot, cross]
    linear_combination (-b.x * b.y * v.y - b.x * b.z * v.z + b.y ^ 2 * v.x + b.z ^ 2 * v.x) * h1 +
      (-a.x ^ 2 * v.x - a.x * a.y * v.y - a.x * a.z * v.z + v.x) * h2 +
      (a.x * b.x * v.x + a.x * b.y * v.y + a.x * b.z * v.z + a.y * b.x * v.y - a.y * b.y * v.x +
        a.z * b.x * v.z - a.z * b.z * v.x) * h3
  · simp only [comb, dot, cross]
    linear_combination (b.x ^ 2 * v.y - b.x * b.y * v.x - b.y * b.z * v.z + b.z ^ 2 * v.y) * h1 +
      (-a.x * a.y * v.x - a.y ^ 2 * v.y - a.y * a.z * v.z + v.y) * h2 +
      (-a.x * b.x * v.y + a.x * b.y * v.x + a.y * b.x * v.x + a.y * b.y * v.y + a.y * b.z * v.z +
        a.z * b.y * v.z - a.z * b.z * v.y) * h3
  · simp only [comb, dot, cross]
    linear_combination (-b.x * b.z * v.x - b.y * b.z * v.y - b.z ^ 2 * v.z + v.z) * h1 +
      (a.x ^ 2 * v.z - a.x * a.z * v.x + a.y ^ 2 * v.z - a.y * a.z * v.y) * h2 +
      (-a.x * b.x * v.z + a.x * b.z * v.x - a.y * b.y * v.z + a.y * b.z * v.y + a.z * b.x * v.x +
        a.z * b.y * v.y + a.z * b.z * v.z) * h3

theorem dot_comb1 (c1 c2 c3 : ℝ) : dot t.e1 (comb c1 c2 c3 t.e1 t.e2 t.e3) = c1 := by
  have e : dot t.e1 (comb c1 c2 c3 t.e1 t.e2 t.e3) =
      c1 * dot t.e1 t.e1 + c2 * dot t.e1 t.e2 + c3 * dot t.e1 t.e3 := by
    simp only [dot, comb]; ring
  rw [e, g.n1, g.o12, g.o13]; ring

theorem dot_comb2 (c1 c2 c3 : ℝ) : dot t.e2 (comb c1 c2 c3 t.e1 t.e2 t.e3) = c2 := by
  have e : dot t.e2 (comb c1 c2 c3 t.e1 t.e2 t.e3) =
      c1 * dot t.e1 t.e2 + c2 * dot t.e2 t.e2 + c3 * dot t.e2 t.e3 := by
    simp only [dot, comb]; ring
  rw [e, g.n2, g.o12, g.o23]; ring

theorem dot_comb3 (c1 c2 c3 : ℝ) : dot t.e3 (comb c1 c2 c3 t.e1 t.e2 t.e3) = c3 := by
  have e : dot t.e3 (comb c1 c2 c3 t.e1 t.e2 t.e3) =
      c1 * dot t.e1 t.e3 + c2 * dot t.e2 t.e3 + c3 * dot t.e3 t.e3 := by
    simp only [dot, comb]; ring
  rw [e, g.n3, g.o13, g.o23]; ring

/-- The dot product of two combinations of a good frame is that of their coefficients. -/
theorem dot_comb (a1 a2 a3 c1 c2 c3 : ℝ) :
    dot (comb a1 a2 a3 t.e1 t.e2 t.e3) (comb c1 c2 c3 t.e1 t.e2 t.e3) =
      a1 * c1 + a2 * c2 + a3 * c3 := by
  have e : dot (comb a1 a2 a3 t.e1 t.e2 t.e3) (comb c1 c2 c3 t.e1 t.e2 t.e3) =
      a1 * dot t.e1 (comb c1 c2 c3 t.e1 t.e2 t.e3) + a2 * dot t.e2 (comb c1 c2 c3 t.e1 t.e2 t.e3) +
        a3 * dot t.e3 (comb c1 c2 c3 t.e1 t.e2 t.e3) := by
    simp only [dot, comb]; ring
  rw [e, g.dot_comb1, g.dot_comb2, g.dot_comb3]

theorem cross23 : cross t.e2 t.e3 = t.e1 := by
  have h1 := g.n1
  have h2 := g.n2
  have h3 := g.o12
  rw [g.e3]
  simp only [dot] at h1 h2 h3
  ext <;> simp only [cross]
  · linear_combination t.e1.x * h2 - t.e2.x * h3
  · linear_combination t.e1.y * h2 - t.e2.y * h3
  · linear_combination t.e1.z * h2 - t.e2.z * h3

theorem cross31 : cross t.e3 t.e1 = t.e2 := by
  have h1 := g.n1
  have h2 := g.n2
  have h3 := g.o12
  rw [g.e3]
  simp only [dot] at h1 h2 h3
  ext <;> simp only [cross]
  · linear_combination t.e2.x * h1 - t.e1.x * h3
  · linear_combination t.e2.y * h1 - t.e1.y * h3
  · linear_combination t.e2.z * h1 - t.e1.z * h3

/-- The cross product of two combinations of a good frame is the combination of the cross
product of their coefficients. -/
theorem cross_comb (a1 a2 a3 c1 c2 c3 : ℝ) :
    cross (comb a1 a2 a3 t.e1 t.e2 t.e3) (comb c1 c2 c3 t.e1 t.e2 t.e3) =
      comb (a2 * c3 - a3 * c2) (a3 * c1 - a1 * c3) (a1 * c2 - a2 * c1) t.e1 t.e2 t.e3 := by
  have e : cross (comb a1 a2 a3 t.e1 t.e2 t.e3) (comb c1 c2 c3 t.e1 t.e2 t.e3) =
      comb (a2 * c3 - a3 * c2) (a3 * c1 - a1 * c3) (a1 * c2 - a2 * c1)
        (cross t.e2 t.e3) (cross t.e3 t.e1) (cross t.e1 t.e2) := by
    ext <;> simp only [cross, comb] <;> ring
  rw [e, g.cross23, g.cross31, ← g.e3]

end Frame.Good

/-! ### The map between two frames -/

section Map

variable {t s : Frame}

theorem map_comb (gt : t.Good) (c1 c2 c3 : ℝ) :
    Frame.map t s (comb c1 c2 c3 t.e1 t.e2 t.e3) = comb c1 c2 c3 s.e1 s.e2 s.e3 := by
  rw [Frame.map, gt.dot_comb1, gt.dot_comb2, gt.dot_comb3]

theorem comb_100 (a b c : Vec) : comb 1 0 0 a b c = a := by ext <;> simp only [comb] <;> ring

theorem comb_010 (a b c : Vec) : comb 0 1 0 a b c = b := by ext <;> simp only [comb] <;> ring

theorem comb_001 (a b c : Vec) : comb 0 0 1 a b c = c := by ext <;> simp only [comb] <;> ring

theorem map_e1 (gt : t.Good) : Frame.map t s t.e1 = s.e1 := by
  rw [Frame.map, gt.n1, dot_comm t.e2, gt.o12, dot_comm t.e3, gt.o13, comb_100]

theorem map_e2 (gt : t.Good) : Frame.map t s t.e2 = s.e2 := by
  rw [Frame.map, gt.o12, gt.n2, dot_comm t.e3, gt.o23, comb_010]

theorem map_e3 (gt : t.Good) : Frame.map t s t.e3 = s.e3 := by
  rw [Frame.map, gt.o13, gt.o23, gt.n3, comb_001]

/-- The map between two good frames preserves dot products. -/
theorem map_dot (gt : t.Good) (gs : s.Good) (v w : Vec) :
    dot (Frame.map t s v) (Frame.map t s w) = dot v w := by
  rw [Frame.map, Frame.map, gs.dot_comb, ← gt.dot_comb, gt.expand, gt.expand]

/-- The map between two good frames preserves cross products. -/
theorem map_cross (gt : t.Good) (gs : s.Good) (v w : Vec) :
    Frame.map t s (cross v w) = cross (Frame.map t s v) (Frame.map t s w) := by
  conv_lhs => rw [← gt.expand v, ← gt.expand w, gt.cross_comb, map_comb gt]
  rw [Frame.map, Frame.map, gs.cross_comb]

end Map

/-! ### TRIAD -/

section Triad

variable {b1 b2 r1 r2 : Vec}

/-- `α u + β v`. -/
def plane (α β : ℝ) (u v : Vec) : Vec := ⟨α * u.x + β * v.x, α * u.y + β * v.y, α * u.z + β * v.z⟩

theorem triad_good (hb1 : 0 < norm b1) (hb : 0 < norm (cross b1 b2)) :
    (frame b1 b2).Good := frame_good hb1 hb

/-- **TRIAD maps the first measurement to the first reference.** -/
theorem triad_first (hb1 : 0 < norm b1) (hb : 0 < norm (cross b1 b2)) :
    triadMap b1 b2 r1 r2 (unit b1) = unit r1 :=
  map_e1 (frame_good hb1 hb)

/-- **TRIAD preserves dot products.** -/
theorem triad_dot (hb1 : 0 < norm b1) (hb : 0 < norm (cross b1 b2)) (hr1 : 0 < norm r1)
    (hr : 0 < norm (cross r1 r2)) (v w : Vec) :
    dot (triadMap b1 b2 r1 r2 v) (triadMap b1 b2 r1 r2 w) = dot v w :=
  map_dot (frame_good hb1 hb) (frame_good hr1 hr) v w

/-- **TRIAD preserves cross products**, so with `triad_dot` it is a rotation. -/
theorem triad_cross (hb1 : 0 < norm b1) (hb : 0 < norm (cross b1 b2)) (hr1 : 0 < norm r1)
    (hr : 0 < norm (cross r1 r2)) (v w : Vec) :
    triadMap b1 b2 r1 r2 (cross v w) = cross (triadMap b1 b2 r1 r2 v) (triadMap b1 b2 r1 r2 w) :=
  map_cross (frame_good hb1 hb) (frame_good hr1 hr) v w

/-- `a × (a × b) = (a · b) a - (a · a) b`. -/
theorem cross_cross_self (a b : Vec) :
    cross a (cross a b) = plane (dot a b) (-dot a a) a b := by
  ext <;> simp only [cross, plane, dot] <;> ring

/-- The triple product `(a × n) · b = -(n · (a × b))`. -/
theorem dot_cross_triple (a n b : Vec) : dot (cross a n) b = -dot n (cross a b) := by
  simp only [dot, cross]; ring

theorem dot_unit_self_eq (c : Vec) : dot (unit c) c = norm c := by
  rw [unit, dot_smul_left, ← norm_sq]
  by_cases h : norm c = 0
  · rw [h]; ring
  · field_simp

/-- **TRIAD maps the second measurement into the plane of the references**, on the side of the
second reference: `T b̄2 = α r̄1 + β r̄2` with `β = |b̄1 × b̄2| / |r̄1 × r̄2| > 0`. -/
theorem triad_second (hb1 : 0 < norm b1) (hb2 : 0 < norm b2) (hb : 0 < norm (cross b1 b2))
    (hr1 : 0 < norm r1) (hr2 : 0 < norm r2) (hr : 0 < norm (cross r1 r2)) :
    let β := norm (cross (unit b1) (unit b2)) / norm (cross (unit r1) (unit r2))
    0 < β ∧ triadMap b1 b2 r1 r2 (unit b2) =
      plane (dot (unit b1) (unit b2) - β * dot (unit r1) (unit r2)) β (unit r1) (unit r2) := by
  intro β
  have hcb : 0 < norm (cross (unit b1) (unit b2)) := by
    rw [cross_unit_unit, norm_smul, abs_of_pos (by positivity)]; positivity
  have hcr : 0 < norm (cross (unit r1) (unit r2)) := by
    rw [cross_unit_unit, norm_smul, abs_of_pos (by positivity)]; positivity
  refine ⟨div_pos hcb hcr, ?_⟩
  have g := frame_good hb1 hb
  have e2 : dot (frame b1 b2).e2 (unit b2) = 0 := by
    show dot (unit (cross b1 b2)) (unit b2) = 0
    rw [← unit_cross_unit hb1 hb2, unit, dot_smul_left, dot_comm, dot_cross_right]; ring
  have e3 : dot (frame b1 b2).e3 (unit b2) = -norm (cross (unit b1) (unit b2)) := by
    show dot (cross (unit b1) (unit (cross b1 b2))) (unit b2) = _
    rw [← unit_cross_unit hb1 hb2, dot_cross_triple, dot_unit_self_eq]
  have hs3 : (frame r1 r2).e3 = plane (dot (unit r1) (unit r2) / norm (cross (unit r1) (unit r2)))
      (-1 / norm (cross (unit r1) (unit r2))) (unit r1) (unit r2) := by
    show cross (unit r1) (unit (cross r1 r2)) = _
    have ha := dot_unit_self hr1
    rw [← unit_cross_unit hr1 hr2]
    generalize unit r1 = a at ha ⊢
    generalize unit r2 = b
    have e : unit (cross a b) = smul (1 / norm (cross a b)) (cross a b) := rfl
    rw [e, cross_smul_right, cross_cross_self, ha]
    ext <;> simp only [smul, plane] <;> ring
  have e1 : (frame b1 b2).e1 = unit b1 := rfl
  rw [triadMap, Frame.map, e2, e3, hs3, e1]
  show comb _ 0 _ (unit r1) (unit (cross r1 r2)) _ = _
  simp only [β]
  ext <;> simp only [comb, plane] <;> field_simp <;> ring

end Triad

end Demos.Attitude
