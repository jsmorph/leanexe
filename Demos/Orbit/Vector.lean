import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
Vectors of three real coordinates with the dot and cross products, for the two-body model of the
orbit-determination demo.  The identities below hold for all vectors and follow from `ring` on
the coordinates.
-/

namespace Demos.Orbit

/-- A vector of three real coordinates. -/
@[ext] structure V3 where
  x : ℝ
  y : ℝ
  z : ℝ

namespace V3

instance : Add V3 := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩
instance : Sub V3 := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩
instance : Neg V3 := ⟨fun a => ⟨-a.x, -a.y, -a.z⟩⟩
instance : SMul ℝ V3 := ⟨fun c a => ⟨c * a.x, c * a.y, c * a.z⟩⟩
instance : Zero V3 := ⟨⟨0, 0, 0⟩⟩

@[simp] theorem add_x (a b : V3) : (a + b).x = a.x + b.x := rfl
@[simp] theorem add_y (a b : V3) : (a + b).y = a.y + b.y := rfl
@[simp] theorem add_z (a b : V3) : (a + b).z = a.z + b.z := rfl
@[simp] theorem sub_x (a b : V3) : (a - b).x = a.x - b.x := rfl
@[simp] theorem sub_y (a b : V3) : (a - b).y = a.y - b.y := rfl
@[simp] theorem sub_z (a b : V3) : (a - b).z = a.z - b.z := rfl
@[simp] theorem neg_x (a : V3) : (-a).x = -a.x := rfl
@[simp] theorem neg_y (a : V3) : (-a).y = -a.y := rfl
@[simp] theorem neg_z (a : V3) : (-a).z = -a.z := rfl
@[simp] theorem smul_x (c : ℝ) (a : V3) : (c • a).x = c * a.x := rfl
@[simp] theorem smul_y (c : ℝ) (a : V3) : (c • a).y = c * a.y := rfl
@[simp] theorem smul_z (c : ℝ) (a : V3) : (c • a).z = c * a.z := rfl
@[simp] theorem zero_x : (0 : V3).x = 0 := rfl
@[simp] theorem zero_y : (0 : V3).y = 0 := rfl
@[simp] theorem zero_z : (0 : V3).z = 0 := rfl

/-- The dot product. -/
def dot (a b : V3) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z

/-- The cross product. -/
def cross (a b : V3) : V3 :=
  ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

/-- The Euclidean length. -/
noncomputable def norm (a : V3) : ℝ := √(dot a a)

@[simp] theorem cross_x (a b : V3) : (cross a b).x = a.y * b.z - a.z * b.y := rfl
@[simp] theorem cross_y (a b : V3) : (cross a b).y = a.z * b.x - a.x * b.z := rfl
@[simp] theorem cross_z (a b : V3) : (cross a b).z = a.x * b.y - a.y * b.x := rfl

theorem dot_self_nonneg (a : V3) : 0 ≤ dot a a := by
  unfold dot; nlinarith [mul_self_nonneg a.x, mul_self_nonneg a.y, mul_self_nonneg a.z]

theorem norm_sq (a : V3) : norm a ^ 2 = dot a a := Real.sq_sqrt (dot_self_nonneg a)

theorem norm_nonneg (a : V3) : 0 ≤ norm a := Real.sqrt_nonneg _

theorem eq_zero_of_dot_self {a : V3} (h : dot a a = 0) : a = 0 := by
  unfold dot at h
  have hx : a.x = 0 := by nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]
  have hy : a.y = 0 := by nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]
  have hz : a.z = 0 := by nlinarith [sq_nonneg a.x, sq_nonneg a.y, sq_nonneg a.z]
  ext <;> simp [hx, hy, hz]

theorem dot_comm (a b : V3) : dot a b = dot b a := by unfold dot; ring

theorem dot_add (a b c : V3) : dot a (b + c) = dot a b + dot a c := by
  simp only [dot, add_x, add_y, add_z]; ring

theorem dot_smul (a b : V3) (c : ℝ) : dot a (c • b) = c * dot a b := by
  simp only [dot, smul_x, smul_y, smul_z]; ring

theorem cross_smul (a b : V3) (c : ℝ) : cross a (c • b) = c • cross a b := by
  ext <;> simp <;> ring

theorem smul_cross (a b : V3) (c : ℝ) : cross (c • a) b = c • cross a b := by
  ext <;> simp <;> ring

theorem cross_add (a b c : V3) : cross a (b + c) = cross a b + cross a c := by
  ext <;> simp <;> ring

/-- `a · (a × b) = 0`. -/
theorem dot_cross_self (a b : V3) : dot a (cross a b) = 0 := by
  simp only [dot, cross_x, cross_y, cross_z]; ring

/-- `b · (a × b) = 0`. -/
theorem dot_cross_self' (a b : V3) : dot b (cross a b) = 0 := by
  simp only [dot, cross_x, cross_y, cross_z]; ring

/-- The cyclic symmetry of the triple product. -/
theorem dot_cross_cycle (a b c : V3) : dot a (cross b c) = dot b (cross c a) := by
  simp only [dot, cross_x, cross_y, cross_z]; ring

/-- `(a × b) × c = (a · c) b - (b · c) a`. -/
theorem cross_cross_left (a b c : V3) :
    cross (cross a b) c = dot a c • b - dot b c • a := by
  ext <;> simp [dot] <;> ring

/-- `a × (b × c) = (a · c) b - (a · b) c`. -/
theorem cross_cross_right (a b c : V3) :
    cross a (cross b c) = dot a c • b - dot a b • c := by
  ext <;> simp [dot] <;> ring

/-- A vector whose cross product with `h ≠ 0` vanishes is a multiple of `h`. -/
theorem eq_smul_of_cross {w h : V3} (hh : 0 < dot h h) (hw : cross w h = 0) :
    w = (dot w h / dot h h) • h := by
  have key : dot h h • w = dot w h • h + cross h (cross w h) := by
    ext <;> simp [dot] <;> ring
  rw [hw] at key
  have hz : cross h (0 : V3) = 0 := by ext <;> simp
  rw [hz] at key
  have hne : dot h h ≠ 0 := hh.ne'
  ext
  · have := congrArg V3.x key
    simp at this
    show w.x = dot w h / dot h h * h.x
    field_simp
    linarith
  · have := congrArg V3.y key
    simp at this
    show w.y = dot w h / dot h h * h.y
    field_simp
    linarith
  · have := congrArg V3.z key
    simp at this
    show w.z = dot w h / dot h h * h.z
    field_simp
    linarith

/-- The cross product of two vectors normal to `h ≠ 0` is a multiple of `h`. -/
theorem cross_eq_smul {a b h : V3} (hh : 0 < dot h h) (ha : dot a h = 0) (hb : dot b h = 0) :
    cross a b = (dot (cross a b) h / dot h h) • h := by
  apply eq_smul_of_cross hh
  rw [cross_cross_left, ha, hb]
  ext <;> simp

end V3

end Demos.Orbit
