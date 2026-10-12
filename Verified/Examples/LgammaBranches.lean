import Verified.Examples.Lgamma

/-!
The selection of the branches of `Lgamma.lgammaWith`.  `bigPath` repeats the code of the branch for
the infinities, NaN, and the magnitudes from `0x1.754d9278b51a6p+1014` on, and `lgamma_big` selects
it.  `lgamma_pole` and `lgamma_unit` select the constant results at the poles and at 1 and 2.  The
proofs rewrite with the equation `lgammaWith.eq_1` and the code's own tests and never unfold the
whole body with `simp`: `extract_lets` turns the `let` bindings of the lower branches into local
definitions, which keeps the term's size, while `dsimp only` and `simp only` on that body did not
finish in four minutes.  The tables are arbitrary arrays.
-/

namespace Verified.Examples.LgammaBranches
open Verified.Examples.Lgamma
open Verified.Examples.Tgamma (floorF)

/-- `±∞`, NaN, and the magnitudes from `0x1.754d9278b51a6p+1014` on. -/
def bigPath (x : Float) : Float × Float :=
  if x.toBits == 0x7F5754D9278B51A6 then
    (Float.ofBits 0x7FEFFFFFFFFFFFFE - Float.ofBits 0x7C80000000000000, 1.0)
  else if x.toBits == 0x7F5754D9278B51A7 then
    (Float.ofBits 0x7FEFFFFFFFFFFFFF - Float.ofBits 0x7C80000000000000, 1.0)
  else if x.toBits <<< 1 ≥ 0xFFE0000000000000 then
    (if x.toBits <<< 1 == 0xFFE0000000000000 then x.abs else x + x, 1.0)
  else if x.toBits >>> 63 == 1 then (1.0 / 0.0, 1.0)
  else (Float.ofBits 0x7FEF000000000000 * Float.ofBits 0x7FEF000000000000, 1.0)

section
variable (logTab hTab sinTab asymTab accTab dbTab tab : Array UInt64) (x : Float)

theorem lgamma_big (h1 : x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C) :
    lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x = bigPath x := by
  rw [lgammaWith.eq_1, ite_eq_left h1]
  rfl

theorem lgamma_pole (h1 : ¬ x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C)
    (h2 : (floorF x == x && x ≤ 0.0) = true) :
    lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x =
      (1.0 / 0.0, if x.toBits >>> 63 == 1 then -1.0 else 1.0) := by
  rw [lgammaWith.eq_1, ite_eq_right h1]
  extract_lets fx
  have h2' : (fx == x && x ≤ 0.0) = true := h2
  rw [ite_eq_left h2']

theorem lgamma_unit (h1 : ¬ x.toBits <<< 1 ≥ 0xFEAEA9B24F16A34C)
    (h2 : ¬ (floorF x == x && x ≤ 0.0) = true)
    (h3 : (floorF x == x && (x == 1.0 || x == 2.0)) = true) :
    lgammaWith logTab hTab sinTab asymTab accTab dbTab tab x = (0.0, 1.0) := by
  rw [lgammaWith.eq_1, ite_eq_right h1]
  extract_lets fx
  have h2' : ¬ (fx == x && x ≤ 0.0) = true := h2
  have h3' : (fx == x && (x == 1.0 || x == 2.0)) = true := h3
  rw [ite_eq_right h2', ite_eq_left h3']

end

#print axioms lgamma_big
#print axioms lgamma_pole
#print axioms lgamma_unit

end Verified.Examples.LgammaBranches
