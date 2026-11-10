import Demos.Sgp4.Kepler
import Demos.Sgp4.Program
import Library.Numerics.Interval.EncloseAttr
import Library.Numerics.Interval.FunctionsProof

/-!
An interval that contains the root of Kepler's equation.  `root.interval` computes an approximate
root `e` in binary64 from the midpoints of its operands, encloses the residual of `e` and the
least slope `1 - √(a² + b²)` with interval operations, and returns `e` widened by the quotient,
which `Kepler.root_bound` shows to bound the distance of `e` from the root.  The result therefore
does not depend on the accuracy of the approximation.
-/

namespace Demos.Sgp4.Kepler

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

/-- An approximate root of Kepler's equation, by the iteration of the binary64 program with at
most 15 corrections. -/
def approximate (inv half : Array UInt64) (a b u : Float) : Float :=
  (LeanExe.repeatWhile 15 (u, 9999.9, 0.0, 0.0) (fun s => Float.abs s.2.1 ≥ 1.0e-13)
    (keplerStep inv half a b u)).1

set_option linter.unusedVariables false in
/-- An interval that contains the root of `E + b cos E - a sin E = u` for every `a`, `b`, and `u`
in the operands. -/
def root.interval (inv half logTab expTab : Array UInt64) (a b u : Interval) : Interval :=
  let e := point (approximate inv half (mid a) (mid b) (mid u))
  let residual := sub (add e (sub (mul b (cosI inv half e)) (mul a (sinI inv half e)))) u
  let slope := sub (ofInt 1) (sqrt (add (sq a) (sq b)))
  let bound := div (abs residual) slope
  if bound.status == 0 then
    if 0 < slope.lo then add e (make (-bound.hi) bound.hi) else rejected
  else rejected

@[enclose] theorem root.encloses {powLog powExp : Array UInt64} {a b u : Interval} {x y z : ℝ}
    (ha : Encloses a x) (hb : Encloses b y) (hu : Encloses u z) :
    Encloses (root.interval Trig.invPi Trig.halfPi powLog powExp a b u) (root x y z) := by
  intro h
  simp only [root.interval] at h ⊢
  generalize approximate Trig.invPi Trig.halfPi (mid a) (mid b) (mid u) = e at h ⊢
  have he : Encloses (point e) (value e.toBits) := fun h => (point_sound h).2
  have hres := encloses_sub (encloses_add he (encloses_sub (encloses_mul hb (encloses_cosI he))
    (encloses_mul ha (encloses_sinI he)))) hu
  have hslope := encloses_sub
    (encloses_ofInt' (n := 1) (m := 1) (q := 1) (by decide +kernel) (by decide +kernel) (by norm_num))
    (encloses_sqrt (encloses_add (encloses_sq ha) (encloses_sq hb)))
  have hbound := encloses_div (encloses_abs hres) hslope
  generalize sub (add (point e) (sub (mul b (cosI Trig.invPi Trig.halfPi (point e)))
    (mul a (sinI Trig.invPi Trig.halfPi (point e))))) u = R at h hbound ⊢
  generalize sub (ofInt 1) (sqrt (add (sq a) (sq b))) = S at h hslope hbound ⊢
  by_cases hb0 : ((div (abs R) S).status == 0) = true
  · by_cases hs0 : 0 < S.lo
    · simp only [hb0, hs0, ite_true] at h ⊢
      obtain ⟨se, sm, hc⟩ := add_sound h
      obtain ⟨-, -, -, hmk⟩ := make_sound sm
      have cB := hbound (beq_iff_eq.mp hb0)
      obtain ⟨-, sS, -⟩ := div_sound (beq_iff_eq.mp hb0)
      have cS := hslope sS
      obtain ⟨z0, zv⟩ := zero_value
      have spos : 0 < 1 - Real.sqrt (x * x + y * y) := by
        have := (lt_iff_value z0 cS.2.1).mp hs0
        rw [zv] at this
        exact lt_of_lt_of_le this cS.2.2.2.1
      have hlt : x ^ 2 + y ^ 2 < 1 := by
        have h1 : Real.sqrt (x * x + y * y) < 1 := by linarith
        have := (Real.sqrt_lt' one_pos).mp h1
        nlinarith
      have rb := root_bound hlt z (value e.toBits)
      have e1 : lhs x y (value e.toBits) - z = value e.toBits +
          (y * Real.cos (value e.toBits) - x * Real.sin (value e.toBits)) - z := by
        unfold lhs; ring
      have e2 : x ^ 2 + y ^ 2 = x * x + y * y := by ring
      rw [e1, e2] at rb
      have habs := abs_le.mp (rb.trans cB.2.2.2.2)
      obtain ⟨-, vn⟩ := neg_value cB.2.2.1
      have hr := hc (value e.toBits) (root x y z - value e.toBits) (he se)
        (hmk _ (by rw [vn]; linarith [habs.2]) (by linarith [habs.1]))
      rwa [add_sub_cancel] at hr
    · simp only [hb0, hs0, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hb0, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

end Demos.Sgp4.Kepler
