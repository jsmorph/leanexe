import Verified.Examples.TgammaMul
import Verified.Examples.TgammaLogdTab

/-!
`Tgamma.fastSum` with a zero first operand.  `fastSum_spec'` extends `TgammaDD.fastSum_spec` to
that case, which occurs at the ends of the table of `Tgamma.asSinpid`, where `sin 0 = 0` makes the
sine product zero and `cos (π/2) = 0` makes the table's `sh` zero.  `fastTwoSum_zero` shows that
`fastTwoSum 0 y` returns `y` and zero, and `value_zero_of_small` that a finite word below `2^-1074`
in magnitude is zero.
-/

namespace Verified.Examples.TgammaSinpidSum
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaLogdTab

set_option exponentiation.threshold 4096

/-- A finite word below `2^-1074` in magnitude is zero. -/
theorem value_zero_of_small (w : UInt64) (h : |value w| < 1 / 2 ^ 1074) : value w = 0 := by
  rw [value_eq] at h ⊢
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 1074),
    div_lt_div_iff_of_pos_right (by positivity), ← Int.cast_abs] at h
  have h1 : |sv w| < 1 := by exact_mod_cast h
  have h0 : sv w = 0 := by rw [abs_lt] at h1; omega
  rw [h0]; simp

/-- **`fastTwoSum` with a zero first operand** returns the second operand and zero. -/
theorem fastTwoSum_zero (x y : Float) (hx : Finite x.toBits) (hy : Finite y.toBits)
    (h0 : value x.toBits = 0) (hlim : |value y.toBits| < 2 ^ 898) :
    Finite (fastTwoSum x y).1.toBits ∧ Finite (fastTwoSum x y).2.toBits ∧
      value (fastTwoSum x y).1.toBits = value y.toBits ∧ value (fastTwoSum x y).2.toBits = 0 := by
  have hl : |value y.toBits| < 2 ^ 1023 := hlim.trans (by norm_num)
  obtain ⟨hsf, hsv⟩ := fadd_exact x y y hx hy hy (by rw [h0, zero_add]) (by rw [h0, zero_add]; exact hl)
  rw [h0, zero_add] at hsv
  obtain ⟨hzf, hzv⟩ := fsub_exact (x + y) x (x + y) hsf hx hsf (by rw [h0, sub_zero])
    (by rw [h0, sub_zero, hsv]; exact hl)
  rw [h0, sub_zero, hsv] at hzv
  obtain ⟨htf, htv⟩ := fsub_exact y (x + y - x) x hy hzf hx (by rw [h0, hzv, sub_self])
    (by rw [hzv, sub_self, abs_zero]; norm_num)
  rw [hzv, sub_self] at htv
  have h1 : (fastTwoSum x y).1 = x + y := rfl
  have h2 : (fastTwoSum x y).2 = y - (x + y - x) := rfl
  rw [h1, h2]
  exact ⟨hsf, htf, hsv, htv⟩

/-- **`fastSum`** for `|yh| ≤ |xh|` or `xh = 0`. -/
theorem fastSum_spec' (xh xl yh yl : Float) (hxh : Finite xh.toBits) (hxl : Finite xl.toBits)
    (hyh : Finite yh.toBits) (hyl : Finite yl.toBits)
    (hxy : |value yh.toBits| ≤ |value xh.toBits| ∨ value xh.toBits = 0)
    (hlim : |value xh.toBits| < 2 ^ 898) (hlimy : |value yh.toBits| < 2 ^ 898)
    (L : ℝ) (hL : |value xl.toBits| + |value yl.toBits| ≤ L) (hLmax : L ≤ 2 ^ 800) :
    Finite (fastSum xh xl yh yl).1.toBits ∧ Finite (fastSum xh xl yh yl).2.toBits ∧
      |value (fastSum xh xl yh yl).1.toBits + value (fastSum xh xl yh yl).2.toBits -
          (value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits))|
        ≤ (3 * L + |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074) / 2 ^ 53 ∧
      |value (fastSum xh xl yh yl).2.toBits| ≤
        L * (1 + 1 / 2 ^ 51) + |value (fastSum xh xl yh yl).1.toBits| / 2 ^ 51 + 1 / 2 ^ 1073 := by
  rcases hxy with hxy | h0
  · exact fastSum_spec xh xl yh yl hxh hxl hyh hyl hxy hlim L hL hLmax
  obtain ⟨hsf, hlf, hsv, htv⟩ := fastTwoSum_zero xh yh hxh hyh h0 hlimy
  have hsum : value (fastTwoSum xh yh).1.toBits + value (fastTwoSum xh yh).2.toBits =
      value xh.toBits + value yh.toBits := by rw [hsv, htv, h0]; ring
  have hsl : |value (fastTwoSum xh yh).2.toBits| ≤
      |value (fastTwoSum xh yh).1.toBits| / 2 ^ 52 + 1 / 2 ^ 1074 := by
    rw [htv, abs_zero]; positivity
  have hsh : |value (fastTwoSum xh yh).1.toBits| ≤ 2 ^ 900 := by
    rw [hsv]; exact hlimy.le.trans (by norm_num)
  obtain ⟨hf, he, hb⟩ := low_sum _ _ xl yl _ hlf hsum hsl hxl hyl L hL hLmax hsh
  simp only [fastSum]
  refine ⟨hsf, hf, ?_, hb⟩
  rw [show value xh.toBits + value xl.toBits + (value yh.toBits + value yl.toBits) =
    value xh.toBits + value yh.toBits + value xl.toBits + value yl.toBits by ring]
  exact he

#print axioms fastSum_spec'

end Verified.Examples.TgammaSinpidSum
