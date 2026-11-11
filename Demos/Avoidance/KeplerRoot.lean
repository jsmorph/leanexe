import Demos.Sgp4.KeplerBox

/-!
An interval that contains the root of Kepler's equation in the form of SGP4,
`E + b cos E - a sin E = u`.  `keplerRootI` is `Demos.Sgp4.Kepler.rootI` with the sum `a² + b²`
clamped at zero before its square root: the outward-rounded square of an interval that holds 0 has
a lower end below zero, which `sqrt` rejects, so `rootI` rejects every state whose `a` and `b`
both hold 0, such as a circular orbit.  `Demos.Sgp4.Kepler.root_bound` bounds the distance of the
approximate root from the root by its residual over the least slope `1 - √(a² + b²)`.
-/

namespace Demos.Avoidance

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)
open Demos.Sgp4

/-- The root of `E + b cos E - a sin E = u` when `a² + b² < 1`. -/
noncomputable def keplerRoot (a b u : ℝ) : ℝ := Kepler.root a b u

set_option linter.unusedVariables false in
/-- An interval that contains the root of `E + b cos E - a sin E = u` for every `a`, `b`, and `u`
in the operands. -/
def keplerRootI (inv half logTab expTab : Array UInt64) (a b u : Interval) : Interval :=
  let e := point (Kepler.approximate inv half (mid a) (mid b) (mid u))
  let residual := sub (add e (sub (mul b (cosI inv half e)) (mul a (sinI inv half e)))) u
  let s := add (sq a) (sq b)
  let slope := sub (ofInt 1) (sqrt (clamp s 0 s.hi))
  let bound := div (abs residual) slope
  if bound.status == 0 then
    if 0 < slope.lo then add e (make (-bound.hi) bound.hi) else rejected
  else rejected

@[enclose] theorem keplerRoot.encloses {powLog powExp : Array UInt64} {a b u : Interval}
    {x y z : ℝ} (ha : Encloses a x) (hb : Encloses b y) (hu : Encloses u z) :
    Encloses (keplerRootI Trig.invPi Trig.halfPi powLog powExp a b u) (keplerRoot x y z) := by
  intro h
  simp only [keplerRootI] at h ⊢
  generalize Kepler.approximate Trig.invPi Trig.halfPi (mid a) (mid b) (mid u) = e at h ⊢
  have he : Encloses (point e) (value e.toBits) := fun h => (point_sound h).2
  have hres := encloses_sub (encloses_add he (encloses_sub (encloses_mul hb (encloses_cosI he))
    (encloses_mul ha (encloses_sinI he)))) hu
  have hs := encloses_add (encloses_sq ha) (encloses_sq hb)
  generalize add (sq a) (sq b) = S2 at h hs ⊢
  have hcl : Encloses (clamp S2 0 S2.hi) (x * x + y * y) := by
    intro hc
    obtain ⟨s1, hcs⟩ := clamp_sound hc
    have c := hs s1
    obtain ⟨z0, zv⟩ := zero_value
    exact hcs _ c (by rw [zv]; nlinarith [mul_self_nonneg x, mul_self_nonneg y]) c.2.2.2.2
  have hslope := encloses_sub
    (encloses_ofInt' (n := 1) (m := 1) (q := 1) (by decide +kernel) (by decide +kernel)
      (by norm_num))
    (encloses_sqrt hcl)
  have hbound := encloses_div (encloses_abs hres) hslope
  generalize sub (add (point e) (sub (mul b (cosI Trig.invPi Trig.halfPi (point e)))
    (mul a (sinI Trig.invPi Trig.halfPi (point e))))) u = R at h hbound ⊢
  generalize sub (ofInt 1) (sqrt (clamp S2 0 S2.hi)) = S at h hslope hbound ⊢
  by_cases hb0 : ((div (abs R) S).status == 0) = true
  · by_cases hs0 : 0 < S.lo
    · simp only [hb0, hs0, ite_true] at h ⊢
      obtain ⟨se, sm, hc⟩ := add_sound h
      obtain ⟨-, -, -, hmk⟩ := make_sound sm
      have cB := hbound (beq_iff_eq.mp hb0)
      obtain ⟨-, sS, -⟩ := div_sound (beq_iff_eq.mp hb0)
      have cS := hslope sS
      have spos : 0 < 1 - Real.sqrt (x * x + y * y) := cS.pos_of_lo hs0
      have hlt : x ^ 2 + y ^ 2 < 1 := by
        have h1 : Real.sqrt (x * x + y * y) < 1 := by linarith
        have := (Real.sqrt_lt' one_pos).mp h1
        nlinarith
      have rb := Kepler.root_bound hlt z (value e.toBits)
      have e1 : Kepler.lhs x y (value e.toBits) - z = value e.toBits +
          (y * Real.cos (value e.toBits) - x * Real.sin (value e.toBits)) - z := by
        unfold Kepler.lhs; ring
      have e2 : x ^ 2 + y ^ 2 = x * x + y * y := by ring
      rw [e1, e2] at rb
      have habs := abs_le.mp (rb.trans cB.2.2.2.2)
      obtain ⟨-, vn⟩ := neg_value cB.2.2.1
      have hr := hc (value e.toBits) (keplerRoot x y z - value e.toBits) (he se)
        (hmk _ (by rw [vn]; unfold keplerRoot; linarith [habs.2])
          (by unfold keplerRoot; linarith [habs.1]))
      rwa [add_sub_cancel] at hr
    · simp only [hb0, hs0, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hb0, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

end Demos.Avoidance
