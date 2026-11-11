import Demos.Sgp4.KeplerBox

/-!
An interval that contains the root of Kepler's equation `E - e sin E = M`.  `keplerI` computes an
approximate root in binary64 with `Demos.Sgp4.Kepler.approximate`, encloses its residual, and
widens it by the residual over the least slope `1 - |e|`, which `Demos.Sgp4.Kepler.root_bound`
shows to bound its distance from the root.  `Demos.Sgp4.Kepler.rootI` computes the same slope as
`1 - √(e² + 0²)`, whose outward-rounded square root rejects `e = 0`, so the circular orbits that
this demo accepts need the absolute value.
-/

namespace Demos.Screening

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)
open Demos.Sgp4

/-- The root of `E - e sin E = M` when `|e| < 1`. -/
noncomputable def kepler (e M : ℝ) : ℝ := Kepler.root e 0 M

set_option linter.unusedVariables false in
/-- An interval that contains the root of `E - e sin E = M` for every `e` and `M` in the
operands. -/
def keplerI (inv half logTab expTab : Array UInt64) (e u : Interval) : Interval :=
  let x := point (Kepler.approximate inv half (mid e) 0.0 (mid u))
  let residual := sub (sub x (mul e (sinI inv half x))) u
  let slope := sub (ofInt 1) (abs e)
  let bound := div (abs residual) slope
  if bound.status == 0 then
    if 0 < slope.lo then add x (make (-bound.hi) bound.hi) else rejected
  else rejected

@[enclose] theorem kepler.encloses {powLog powExp : Array UInt64} {e u : Interval} {x z : ℝ}
    (he : Encloses e x) (hu : Encloses u z) :
    Encloses (keplerI Trig.invPi Trig.halfPi powLog powExp e u) (kepler x z) := by
  intro h
  simp only [keplerI] at h ⊢
  generalize Kepler.approximate Trig.invPi Trig.halfPi (mid e) 0.0 (mid u) = w at h ⊢
  have hw : Encloses (point w) (value w.toBits) := fun h => (point_sound h).2
  have hres := encloses_sub (encloses_sub hw (encloses_mul he (encloses_sinI hw))) hu
  have hslope := encloses_sub
    (encloses_ofInt' (n := 1) (m := 1) (q := 1) (by decide +kernel) (by decide +kernel)
      (by norm_num))
    (encloses_abs he)
  have hbound := encloses_div (encloses_abs hres) hslope
  generalize sub (sub (point w) (mul e (sinI Trig.invPi Trig.halfPi (point w)))) u = R
    at h hbound ⊢
  generalize sub (ofInt 1) (abs e) = S at h hslope hbound ⊢
  by_cases hb0 : ((div (abs R) S).status == 0) = true
  · by_cases hs0 : 0 < S.lo
    · simp only [hb0, hs0, ite_true] at h ⊢
      obtain ⟨se, sm, hc⟩ := add_sound h
      obtain ⟨-, -, -, hmk⟩ := make_sound sm
      have cB := hbound (beq_iff_eq.mp hb0)
      obtain ⟨-, sS, -⟩ := div_sound (beq_iff_eq.mp hb0)
      have cS := hslope sS
      obtain ⟨z0, zv⟩ := zero_value
      have spos : 0 < 1 - |x| := by
        have := (lt_iff_value z0 cS.2.1).mp hs0
        rw [zv] at this
        exact lt_of_lt_of_le this cS.2.2.2.1
      have hsq : Real.sqrt (x ^ 2 + 0 ^ 2) = |x| := by
        rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq_eq_abs]
      have hlt : x ^ 2 + 0 ^ 2 < 1 := by
        have h1 : |x| < 1 := by linarith
        have := abs_lt.mp h1
        nlinarith
      have rb := Kepler.root_bound hlt z (value w.toBits)
      have e1 : Kepler.lhs x 0 (value w.toBits) - z =
          value w.toBits - x * Real.sin (value w.toBits) - z := by
        unfold Kepler.lhs; ring
      rw [e1, hsq] at rb
      have habs := abs_le.mp (rb.trans cB.2.2.2.2)
      obtain ⟨-, vn⟩ := neg_value cB.2.2.1
      have hr := hc (value w.toBits) (kepler x z - value w.toBits) (hw se)
        (hmk _ (by rw [vn]; unfold kepler; linarith [habs.2])
          (by unfold kepler; linarith [habs.1]))
      rwa [add_sub_cancel] at hr
    · simp only [hb0, hs0, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [hb0, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

end Demos.Screening
