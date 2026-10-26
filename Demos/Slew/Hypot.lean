import Demos.Slew.Axis

/-! The amplitude `√(A² + B²)` of the edge check's sinusoid.  The program computes `√(a a + b b)`
from approximations `a` and `b` of `A` and `B`.  When `a² + b² ≥ 2⁻¹⁰⁰⁰`, the result lies within
`1020 u` of `√(A² + B²)` (`hypot_bnd`): the rounding of the radicand and the square root are
relative, and the length of a vector in the plane changes by at most the sum of its components'
changes (`sqrt_sum_sq_sub_le`, from Minkowski's inequality). -/

namespace Demos.Slew.Hypot

open Demos.Slew.Rounding CodeLib.IEEE64 LeanExe.ProofKit LeanExe.ProofKit.F64Approx

set_option exponentiation.threshold 4096

theorem sqrt_sq_add_sq_le_abs (x y : ℝ) : √(x ^ 2 + y ^ 2) ≤ |x| + |y| := by
  rw [show |x| + |y| = √((|x| + |y|) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  nlinarith [abs_nonneg x, abs_nonneg y, sq_abs x, sq_abs y, mul_nonneg (abs_nonneg x) (abs_nonneg y)]

/-- Minkowski's inequality in the plane. -/
theorem sqrt_add_le (A B x y : ℝ) : √((A + x) ^ 2 + (B + y) ^ 2) ≤ √(A ^ 2 + B ^ 2) + √(x ^ 2 + y ^ 2) := by
  have hP := Real.sqrt_nonneg (A ^ 2 + B ^ 2)
  have hD := Real.sqrt_nonneg (x ^ 2 + y ^ 2)
  have hcs : A * x + B * y ≤ √(A ^ 2 + B ^ 2) * √(x ^ 2 + y ^ 2) := by
    rw [← Real.sqrt_mul (by positivity)]
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg (A * y - B * x)]))
  rw [show √(A ^ 2 + B ^ 2) + √(x ^ 2 + y ^ 2) = √((√(A ^ 2 + B ^ 2) + √(x ^ 2 + y ^ 2)) ^ 2) by
    rw [Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  have e1 := Real.sq_sqrt (show 0 ≤ A ^ 2 + B ^ 2 by positivity)
  have e2 := Real.sq_sqrt (show 0 ≤ x ^ 2 + y ^ 2 by positivity)
  nlinarith

theorem sqrt_sum_sq_sub_le (a b A B : ℝ) : |√(a ^ 2 + b ^ 2) - √(A ^ 2 + B ^ 2)| ≤ |a - A| + |b - B| := by
  rw [abs_le]
  constructor
  · have h := sqrt_add_le a b (A - a) (B - b)
    have h2 := sqrt_sq_add_sq_le_abs (A - a) (B - b)
    simp only [add_sub_cancel] at h
    rw [abs_sub_comm a A, abs_sub_comm b B]
    linarith
  · have h := sqrt_add_le A B (a - A) (b - B)
    have h2 := sqrt_sq_add_sq_le_abs (a - A) (b - B)
    simp only [add_sub_cancel] at h
    linarith

theorem square_approx3 {x : Float} (hx : Fin x) (hb : |val x| ≤ 3) :
    FApprox (x * x) (val x * val x) (val x * val x / 2 ^ 53 + 1 / 2 ^ 1075) := by
  have h := fapprox_mul (fapprox_val hx) (fapprox_val hx) |val x| |val x| le_rfl le_rfl
    (|val x| * |val x|) (by simp) (by nlinarith [abs_nonneg (val x)])
  have e : (0 : ℝ) * |val x| + |val x| * 0 + 0 * 0 + |val x| * |val x| / 2 ^ 53 + 1 / 2 ^ 1075 =
      val x * val x / 2 ^ 53 + 1 / 2 ^ 1075 := by
    rw [abs_mul_abs_self]; ring
  rwa [e] at h

set_option maxHeartbeats 1000000 in
/-- The program's `√(a a + b b)` within `1020 u` of `√(A² + B²)`, when `a² + b² ≥ 2⁻¹⁰⁰⁰`. -/
theorem hypot_bnd {a b : Float} {A B ea eb : ℝ} (ha : Bnd a A ea 2.0005) (hb : Bnd b B eb 1.0003)
    (hea : ea ≤ 509.6 / 2 ^ 53) (heb : eb ≤ 503 / 2 ^ 53)
    (hlo : 1 / 2 ^ 1000 ≤ val a * val a + val b * val b) :
    Bnd (Float.sqrt (a * a + b * b)) (√(A ^ 2 + B ^ 2)) (1020 / 2 ^ 53) 2.24 := by
  have hA := ha.2
  have hB := hb.2
  have hav0 : |val a - A| ≤ ea := ha.1.2
  have hbv0 : |val b - B| ≤ eb := hb.1.2
  have hav := abs_le.mp hav0
  have hbv := abs_le.mp hbv0
  have hea0 := ha.err_nonneg
  have heb0 := hb.err_nonneg
  have hA' := abs_le.mp hA
  have hB' := abs_le.mp hB
  set X := val a
  set Y := val b
  have bx : |X| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
  have byy : |Y| ≤ 3 := by rw [abs_le]; constructor <;> nlinarith
  have hX := mul_self_nonneg X
  have hY := mul_self_nonneg Y
  have hX9 : X * X ≤ 9 := by nlinarith [abs_le.mp bx]
  have hY9 : Y * Y ≤ 9 := by nlinarith [abs_le.mp byy]
  have px := square_approx3 ha.1.1 bx
  have py := square_approx3 hb.1.1 byy
  set T := X * X + Y * Y with hT
  have ht := fapprox_add px py (T + ((X * X / 2 ^ 53 + 1 / 2 ^ 1075) + (Y * Y / 2 ^ 53 + 1 / 2 ^ 1075)))
    (by rw [abs_of_nonneg (by linarith)]) (by linarith)
  set et := X * X / 2 ^ 53 + 1 / 2 ^ 1075 + (Y * Y / 2 ^ 53 + 1 / 2 ^ 1075) +
    (T + (X * X / 2 ^ 53 + 1 / 2 ^ 1075 + (Y * Y / 2 ^ 53 + 1 / 2 ^ 1075))) / 2 ^ 53 with het
  have hpos : 0 < T := lt_of_lt_of_le (by norm_num) hlo
  have het1 : et ≤ 2.002 / 2 ^ 53 * T := by rw [het]; nlinarith
  have heam : et < T := by nlinarith
  have hs := fapprox_sqrt ht T T hpos le_rfl heam le_rfl _ le_rfl
  set t := √T with htdef
  have ht0 : 0 < t := Real.sqrt_pos.mpr hpos
  have htt : t * t = T := Real.mul_self_sqrt hpos.le
  have h1 : et / t ≤ 2.002 / 2 ^ 53 * t := by
    rw [div_le_iff₀ ht0]; nlinarith
  have h2 : √(T + et) ≤ t * (1 + 2 / 2 ^ 53) := by
    rw [show t * (1 + 2 / 2 ^ 53) = √((t * (1 + 2 / 2 ^ 53)) ^ 2) by
      rw [Real.sqrt_sq (by positivity)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hrel : |value (Float.sqrt (a * a + b * b)).toBits - t| ≤ 3.1 / 2 ^ 53 * t := by
    refine hs.2.trans ?_
    have := add_le_add h1 (div_le_div_of_nonneg_right h2 (show (0 : ℝ) ≤ 2 ^ 53 by norm_num))
    nlinarith
  -- the change of the length
  have hmink := sqrt_sum_sq_sub_le X Y A B
  rw [show X ^ 2 + Y ^ 2 = T by rw [hT]; ring, ← htdef] at hmink
  have hdiff : |t - √(A ^ 2 + B ^ 2)| ≤ ea + eb := by
    refine hmink.trans (add_le_add ?_ ?_)
    · exact hav0
    · exact hbv0
  have hR : √(A ^ 2 + B ^ 2) ≤ 2.2368 := by
    have h1 : A ^ 2 ≤ 2.0005 ^ 2 := sq_le_sq' hA'.1 hA'.2
    have h2 : B ^ 2 ≤ 1.0003 ^ 2 := sq_le_sq' hB'.1 hB'.2
    rw [show (2.2368 : ℝ) = √(2.2368 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith)
  have htb : t ≤ 2.24 := by linarith [abs_le.mp hdiff]
  refine ⟨⟨hs.1, ?_⟩, ?_⟩
  · calc |value (Float.sqrt (a * a + b * b)).toBits - √(A ^ 2 + B ^ 2)|
        ≤ |value (Float.sqrt (a * a + b * b)).toBits - t| + |t - √(A ^ 2 + B ^ 2)| := abs_sub_le _ _ _
      _ ≤ 3.1 / 2 ^ 53 * 2.24 + (509.6 / 2 ^ 53 + 503 / 2 ^ 53) := by
          apply add_le_add (hrel.trans (by nlinarith)) (hdiff.trans (by linarith))
      _ ≤ 1020 / 2 ^ 53 := by norm_num
  · rw [abs_of_nonneg (Real.sqrt_nonneg _)]; linarith

end Demos.Slew.Hypot
