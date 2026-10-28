import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Real-number definitions for the slew planner's theorems.  A vector is a triple of reals and a
quaternion a quadruple, with explicit formulas rather than Mathlib's quaternions.  `rot q v` is
the program's rotation formula `v + w t + q × t` with `t = 2 q × v` in exact arithmetic, which for
a unit quaternion `q` is the rotation of `v` by `q`.  `rod n φ v` is Rodrigues' formula for the
rotation of `v` by `φ` about the unit axis `n`.  `angle w s` is the rotation angle of a quaternion
with scalar part `w ≥ 0` and vector length `s`, and `Holds` is the predicate of one cone. -/

namespace Demos.Slew.Spec

/-- A vector of three reals. -/
@[ext] structure Vec where
  x : ℝ
  y : ℝ
  z : ℝ

/-- A quaternion `[w, x, y, z]` of reals. -/
@[ext] structure Quat where
  w : ℝ
  x : ℝ
  y : ℝ
  z : ℝ

namespace Vec

def dot (a b : Vec) : ℝ := a.x * b.x + a.y * b.y + a.z * b.z

def cross (a b : Vec) : Vec := ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

def sub (a b : Vec) : Vec := ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

def smul (k : ℝ) (a : Vec) : Vec := ⟨k * a.x, k * a.y, k * a.z⟩

noncomputable def norm (a : Vec) : ℝ := Real.sqrt (dot a a)

/-- `a` scaled to unit length, or the zero vector when `a` is zero. -/
noncomputable def unit (a : Vec) : Vec := smul (1 / norm a) a

end Vec

namespace Quat

def norm2 (q : Quat) : ℝ := q.w * q.w + q.x * q.x + q.y * q.y + q.z * q.z

def smul (k : ℝ) (q : Quat) : Quat := ⟨k * q.w, k * q.x, k * q.y, k * q.z⟩

/-- `q` scaled to unit length. -/
noncomputable def unit (q : Quat) : Quat := smul (1 / Real.sqrt (norm2 q)) q

/-- The program's rotation formula in exact arithmetic: `v + w t + q × t` with `t = 2 q × v`. -/
def rot (q : Quat) (v : Vec) : Vec :=
  let tx := 2 * (q.y * v.z - q.z * v.y)
  let ty := 2 * (q.z * v.x - q.x * v.z)
  let tz := 2 * (q.x * v.y - q.y * v.x)
  ⟨v.x + q.w * tx + (q.y * tz - q.z * ty), v.y + q.w * ty + (q.z * tx - q.x * tz),
    v.z + q.w * tz + (q.x * ty - q.y * tx)⟩

end Quat

open Vec in
/-- Rodrigues' formula: the rotation of `v` by `φ` about the unit axis `n`. -/
noncomputable def rod (n : Vec) (φ : ℝ) (v : Vec) : Vec :=
  let c := Real.cos φ
  let s := Real.sin φ
  let k := dot n v * (1 - c)
  ⟨v.x * c + (cross n v).x * s + n.x * k, v.y * c + (cross n v).y * s + n.y * k,
    v.z * c + (cross n v).z * s + n.z * k⟩

/-- The rotation angle, in `[0, π]`, of a quaternion with scalar part `w ≥ 0` and vector length
`s`: `cos θ = (w² - s²)/(w² + s²)`. -/
noncomputable def angle (w s : ℝ) : ℝ := Real.arccos ((w * w - s * s) / (w * w + s * s))

/-- The vector `v` satisfies the cone of axis `u` and cosine `c`: inside it for a keep-in cone,
outside it for a keep-out cone. -/
def Holds (keepIn : Bool) (u : Vec) (c : ℝ) (v : Vec) : Prop :=
  if keepIn then c ≤ Vec.dot u v else Vec.dot u v ≤ c

end Demos.Slew.Spec
