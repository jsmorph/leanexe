import Demos.Slew.Error

/-! The axis and angle of the relative quaternion `rel` in the edge check.  With `X`, `Y`, `Z`
the real values of `rel`'s vector part, `S² = X² + Y² + Z²`.  The program's radicand
`x x + y y + z z` lies within `3.001 u S² + 4 η` of `S²` (`radicand_approx`), so for
`S² ≥ 2⁻¹⁰⁰⁰` its square root `s` lies within `4.1 u S` of `S` (`s_approx`), a relative bound.
When `s` passes the small-angle threshold, the axis `x/s` lies within `5.2 u` of `X/S`
componentwise (`axis_bnd`), and `w w - s s` and `2 w s` lie within `12.5 u` of `W² - S²` and
`2 W S` (`ct_bnd`, `st_bnd`).  `s_nonneg` shows that an `s` that is not a NaN is not negative. -/

namespace Demos.Slew.Axis

open Demos.Slew.Spec Demos.Slew.Rounding Demos.Slew.Error
open CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx

set_option exponentiation.threshold 4096

/-- The real vector part of a quaternion. -/
noncomputable def vecPart (q : Q4) : Vec := ⟨val q.x, val q.y, val q.z⟩

/-- `S²`, the squared length of `rel`'s vector part. -/
noncomputable def s2 (q : Q4) : ℝ := val q.x * val q.x + val q.y * val q.y + val q.z * val q.z

/-- The program's radicand and its square root. -/
def radicand (q : Q4) : Float := q.x * q.x + q.y * q.y + q.z * q.z
def sOf (q : Q4) : Float := Float.sqrt (radicand q)

theorem s2_eq (q : Q4) : s2 q = Vec.dot (vecPart q) (vecPart q) := rfl

theorem s2_nonneg (q : Q4) : 0 ≤ s2 q := by
  simp only [s2]; nlinarith [mul_self_nonneg (val q.x), mul_self_nonneg (val q.y),
    mul_self_nonneg (val q.z)]

/-- A product of a float with itself, within `u X² + η` of `X²`. -/
theorem square_approx {x : Float} (hx : Fin x) (hb : |val x| ≤ 2) :
    FApprox (x * x) (val x * val x) (val x * val x / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have h := fapprox_mul (fapprox_val hx) (fapprox_val hx) |val x| |val x| le_rfl le_rfl
    (|val x| * |val x|) (by simp) (by nlinarith [abs_nonneg (val x)])
  have e : (0 : ℝ) * |val x| + |val x| * 0 + 0 * 0 + |val x| * |val x| / 2 ^ 53 + 1 / 2 ^ 1075 =
      val x * val x / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [abs_mul_abs_self]; ring
  rwa [e] at h

theorem radicand_approx (q : Q4) (hx : Fin q.x) (hy : Fin q.y) (hz : Fin q.z)
    (bx : |val q.x| ≤ 2) (byy : |val q.y| ≤ 2) (bz : |val q.z| ≤ 2) :
    FApprox (radicand q) (s2 q) (3.001 / 2 ^ 53 * s2 q + 4 / 2 ^ 1075) := by
  set X := val q.x
  set Y := val q.y
  set Z := val q.z
  have hX := mul_self_nonneg X
  have hY := mul_self_nonneg Y
  have hZ := mul_self_nonneg Z
  have hX4 : X * X ≤ 4 := by nlinarith [abs_le.mp bx]
  have hY4 : Y * Y ≤ 4 := by nlinarith [abs_le.mp byy]
  have hZ4 : Z * Z ≤ 4 := by nlinarith [abs_le.mp bz]
  have px := square_approx hx bx
  have py := square_approx hy byy
  have pz := square_approx hz bz
  have sxy := fapprox_add px py (X * X + Y * Y + ((X * X / 2 ^ 53 + 1 / 2 ^ 1075) +
    (Y * Y / 2 ^ 53 + 1 / 2 ^ 1075))) (by rw [abs_of_nonneg (by linarith)]) (by linarith)
  have s := fapprox_add sxy pz (X * X + Y * Y + Z * Z + (((X * X / 2 ^ 53 + 1 / 2 ^ 1075) +
      (Y * Y / 2 ^ 53 + 1 / 2 ^ 1075) + (X * X + Y * Y + ((X * X / 2 ^ 53 + 1 / 2 ^ 1075) +
        (Y * Y / 2 ^ 53 + 1 / 2 ^ 1075))) / 2 ^ 53) + (Z * Z / 2 ^ 53 + 1 / 2 ^ 1075)))
    (by rw [abs_of_nonneg (by linarith)]) (by linarith)
  refine Approx.mono s ?_
  simp only [s2]
  linarith

theorem s_approx (q : Q4) (hx : Fin q.x) (hy : Fin q.y) (hz : Fin q.z)
    (bx : |val q.x| ≤ 2) (byy : |val q.y| ≤ 2) (bz : |val q.z| ≤ 2)
    (hlo : 1 / 2 ^ 1000 ≤ s2 q) :
    FApprox (sOf q) (√(s2 q)) (4.1 / 2 ^ 53 * √(s2 q)) := by
  have hr := radicand_approx q hx hy hz bx byy bz
  set S2 := s2 q with hS2
  have hpos : 0 < S2 := lt_of_lt_of_le (by norm_num) hlo
  have hex : 3.001 / 2 ^ 53 * S2 + 4 / 2 ^ 1075 ≤ 3.002 / 2 ^ 53 * S2 := by nlinarith
  have heam : 3.001 / 2 ^ 53 * S2 + 4 / 2 ^ 1075 < S2 := by nlinarith
  have h := fapprox_sqrt hr S2 S2 hpos le_rfl heam le_rfl _ le_rfl
  refine Approx.mono h ?_
  set t := √S2 with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hpos
  have htt : t * t = S2 := Real.mul_self_sqrt hpos.le
  have hlo' : 1 / 2 ^ 500 ≤ t := by
    rw [ht, show (1 : ℝ) / 2 ^ 500 = √((1 / 2 ^ 500) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num at hlo ⊢; linarith)
  have h1 : (3.001 / 2 ^ 53 * S2 + 4 / 2 ^ 1075) / t ≤ 3.002 / 2 ^ 53 * t := by
    rw [div_le_iff₀ ht0, ← htt]; nlinarith
  have h2 : √(S2 + (3.001 / 2 ^ 53 * S2 + 4 / 2 ^ 1075)) ≤ t * (1 + 2 / 2 ^ 53) := by
    rw [show t * (1 + 2 / 2 ^ 53) = √((t * (1 + 2 / 2 ^ 53)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  calc (3.001 / 2 ^ 53 * S2 + 4 / 2 ^ 1075) / t + √(S2 + (3.001 / 2 ^ 53 * S2 + 4 / 2 ^ 1075)) / 2 ^ 53
      ≤ 3.002 / 2 ^ 53 * t + t * (1 + 2 / 2 ^ 53) / 2 ^ 53 :=
        add_le_add h1 (div_le_div_of_nonneg_right h2 (by norm_num))
    _ ≤ 4.1 / 2 ^ 53 * t := by nlinarith

/-- A float square root that is not a NaN is not negative. -/
theorem sqrt_nonneg_of_lt {r : Float} (hr : Fin r) {b : Float} (h : Float.sqrt r < b) :
    0 ≤ val (Float.sqrt r) := by
  have hbits := F64Bits.toBits_sqrt r
  have hlt := (F64Bits.lt_iff _ _).mp h
  rw [hbits] at hlt
  simp only [val, hbits]
  have hnan := not_nan_of_finite hr
  by_cases hm : Wasm.IEEE64.scaledMagnitude r.toBits = 0
  · have e : Wasm.IEEE64.sqrt r.toBits = r.toBits := by
      unfold Wasm.IEEE64.sqrt; simp [hnan, hm]
    rw [e]
    have : value r.toBits = 0 := by simp [value, Wasm.IEEE64.scaledValue, hm]
    rw [this]
  · by_cases hs : Wasm.IEEE64.sign r.toBits = true
    · exfalso
      have e : Wasm.IEEE64.sqrt r.toBits = Wasm.IEEE64.canonicalNaN := by
        unfold Wasm.IEEE64.sqrt; simp [hnan, hm, hs]
      have hc : Wasm.IEEE64.isNaN Wasm.IEEE64.canonicalNaN = true := by decide
      rw [e] at hlt
      simp [Wasm.IEEE64.lt, hc] at hlt
    · have hs' : Wasm.IEEE64.sign r.toBits = false := by simpa using hs
      have hrel := F64SqrtBounds.sqrt_real_relative r.toBits hr hm hs'
      have hu : (unitRoundoff64 : ℝ) = 1 / 2 ^ 53 := rfl
      have hsq := Real.sqrt_nonneg (value r.toBits)
      have := abs_le.mp hrel.2
      rw [hu] at this
      nlinarith [this.1]

/-! ### The axis -/

theorem norm_vecPart (q : Q4) : Vec.norm (vecPart q) = √(s2 q) := rfl

theorem abs_le_sqrt_s2 (q : Q4) :
    |val q.x| ≤ √(s2 q) ∧ |val q.y| ≤ √(s2 q) ∧ |val q.z| ≤ √(s2 q) := by
  refine ⟨Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_, Real.abs_le_sqrt ?_⟩ <;>
    simp only [s2, sq] <;> nlinarith [mul_self_nonneg (val q.x), mul_self_nonneg (val q.y),
      mul_self_nonneg (val q.z)]

/-- One component of the axis `x / s`, within `5.2 u` of `X / S`. -/
theorem axis_component {x s : Float} {S : ℝ} (hx : Fin x) (hS : 0 < S) (hxS : |val x| ≤ S)
    (hs : FApprox s S (4.1 / 2 ^ 53 * S)) : Bnd (x / s) (val x / S) (5.2 / 2 ^ 53) 1 := by
  have hpos : 0 < S - 4.1 / 2 ^ 53 * S := by nlinarith
  have h := fapprox_div (fapprox_val hx) hs S S hxS (le_abs_self S) (by nlinarith)
    (1 / (1 - 4.1 / 2 ^ 53))
    (by rw [show S - 4.1 / 2 ^ 53 * S = S * (1 - 4.1 / 2 ^ 53) by ring, add_zero]
        apply le_of_eq
        field_simp) (by norm_num)
  refine ⟨Approx.mono h ?_, ?_⟩
  · rw [show (0 + S * (4.1 / 2 ^ 53 * S) / S) / (S - 4.1 / 2 ^ 53 * S) =
        4.1 / 2 ^ 53 / (1 - 4.1 / 2 ^ 53) by field_simp; ring]
    norm_num
  · rw [abs_div, abs_of_pos hS, div_le_one hS]; exact hxS

/-- The axis of the program, `(x/s, y/s, z/s)`, within `5.2 u` of the unit axis `v/S`. -/
theorem axis_bnd (q : Q4) (hx : Fin q.x) (hy : Fin q.y) (hz : Fin q.z) (hS : 0 < √(s2 q))
    (hs : FApprox (sOf q) (√(s2 q)) (4.1 / 2 ^ 53 * √(s2 q))) :
    Bnd3 ⟨q.x / sOf q, q.y / sOf q, q.z / sOf q⟩ (Vec.unit (vecPart q)) (5.2 / 2 ^ 53) 1 := by
  obtain ⟨bx, byy, bz⟩ := abs_le_sqrt_s2 q
  have e : ∀ X : ℝ, X / √(s2 q) = 1 / Vec.norm (vecPart q) * X := by
    intro X; rw [norm_vecPart]; ring
  refine ⟨?_, ?_, ?_⟩
  · have h := axis_component hx hS bx hs
    simp only [Vec.unit, Vec.smul]; rw [← e]; exact h
  · have h := axis_component hy hS byy hs
    simp only [Vec.unit, Vec.smul]; rw [← e]; exact h
  · have h := axis_component hz hS bz hs
    simp only [Vec.unit, Vec.smul]; rw [← e]; exact h

/-! ### The cosine and sine of the angle -/

theorem ct_bnd {w s : Float} {S : ℝ} (hw : Bnd w (val w) 0 1.0001) (hs : Bnd s S (4.2 / 2 ^ 53) 1.0001)
    (hQ : val w * val w + S * S ≤ 1.0001) :
    Bnd (w * w - s * s) (val w * val w - S * S) (12.5 / 2 ^ 53) 1.0001 := by
  have h := Bnd.sub (12.5 / 2 ^ 53) (Bnd.mul (1.001 / 2 ^ 53) hw hw (by norm_num) (by norm_num))
    (Bnd.mul (9.41 / 2 ^ 53) hs hs (by norm_num) (by norm_num)) (by norm_num) (by norm_num)
  refine h.rebound ?_
  rw [abs_le]; constructor <;> nlinarith [mul_self_nonneg (val w), mul_self_nonneg S]

theorem st_bnd {w s : Float} {S : ℝ} (hw : Bnd w (val w) 0 1.0001) (hs : Bnd s S (4.2 / 2 ^ 53) 1.0001)
    (hQ : val w * val w + S * S ≤ 1.0001) :
    Bnd (2.0 * w * s) (2 * val w * S) (12.5 / 2 ^ 53) 1.0001 := by
  have h := Bnd.mul (12.5 / 2 ^ 53) (Bnd.mul (2.001 / 2 ^ 53) Bnd.two hw (by norm_num) (by norm_num))
    hs (by norm_num) (by norm_num)
  refine h.rebound ?_
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (val w - S), sq_nonneg (val w + S)]

end Demos.Slew.Axis
