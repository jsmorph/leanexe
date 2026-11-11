import Demos.Sgp4.BoxVerified
import Demos.Sgp4.TleSound
import Demos.Sgp4.OmmSound
import Verified.Master

/-!
The master theorems of the exports of the enclosing SGP4 module `sgp4box`: `sgp4Box` on
intervals, `sgp4BoxAround` on binary64 values, and `Tle.propagate` on the two lines of an element
set.  Each states, for an export called from a ready store with room for its bound, what
`BoxMeets` states of the result for every element set and time that the inputs contain.
-/

namespace Demos.Sgp4

open Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value)

/-- `Tle.propagate` returns status 10 exactly for lines without the layout, and otherwise a result
that meets `BoxMeets` for the element set of the lines. -/
theorem Tle.propagate_meets {logTab expTab s1 s2 : Array UInt64} {t : Interval}
    (h1 : s1.size < 2 ^ 64) (h2 : s2.size < 2 ^ 64) :
    ((Tle.propagateWith Trig.invPi Trig.halfPi logTab expTab s1 s2 t).status = 10 ↔
        ¬Tle.WellFormed s1 s2) ∧
      ∀ t', Encloses t t' → Tle.WellFormed s1 s2 →
        BoxMeets (Tle.propagateWith Trig.invPi Trig.halfPi logTab expTab s1 s2 t)
          (Tle.elements s1 s2) t' := by
  simp only [Tle.propagateWith]
  by_cases hf : ((Tle.read s1 s2).status == 0) = true
  · simp only [hf, ite_true]
    have h0 := beq_iff_eq.mp hf
    have hw := (Tle.read_status s1 s2 h1 h2).mp h0
    refine ⟨⟨fun h10 => ?_, fun hn => absurd hw hn⟩, fun t' ht _ => box_meets
      (Tle.read_encloses s1 s2 h0) ht⟩
    rcases box_status_values logTab expTab (Tle.read s1 s2).n (Tle.read s1 s2).e
      (Tle.read s1 s2).incl (Tle.read s1 s2).node (Tle.read s1 s2).argp (Tle.read s1 s2).m
      (Tle.read s1 s2).bstar t with v | v | v | v | v | v | v | v <;> rw [v] at h10 <;>
      exact absurd h10 (by decide)
  · simp only [hf, Bool.false_eq_true, ite_false]
    have h0 : ¬(Tle.read s1 s2).status = 0 := fun h => hf (beq_iff_eq.mpr h)
    have h10 : (noBox (Tle.read s1 s2).status).status = 10 :=
      (Tle.read_values s1 s2).resolve_left h0
    have hnw : ¬Tle.WellFormed s1 s2 := fun hw => h0 ((Tle.read_status s1 s2 h1 h2).mpr hw)
    exact ⟨⟨fun _ => hnw, fun _ => h10⟩, fun _ _ hw => absurd hw hnw⟩

/-- The export `sgp4Box` returns, for every element set and time in its input intervals, a
result whose intervals of status 0 or 6 contain the model's position and velocity and whose
status other than 7 is the model's. -/
theorem sgp4Box_master :
    Verified.Master boxCompiled.module boxCompiled.tables "sgp4Box" boxCompiled.sgp4Box.bound
      (fun _ => True)
      (fun (x : Interval × Interval × Interval × Interval × Interval × Interval × Interval ×
          Interval) b =>
        ∀ el t', Input x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1 el →
          Encloses x.2.2.2.2.2.2.2 t' → BoxMeets b el t') :=
  .of_trapFree boxCompiled.sgp4Box.trapFree (Verified.tables_at [0, 1, 2, 3] (by decide) rfl)
    (by decide +kernel) (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ _ _ _ _ _ hi ht => box_meets hi ht

/-- The element set of binary64 values, as real numbers. -/
noncomputable def valuesOf (n e incl node argp m bstar : Float) : Model.Elements :=
  ⟨value n.toBits, value e.toBits, value incl.toBits, value node.toBits, value argp.toBits,
    value m.toBits, value bstar.toBits⟩

/-- The export `sgp4BoxAround`, called on binary64 values, returns a result that meets
`BoxMeets` for the element set and the time of those values. -/
theorem sgp4BoxAround_master :
    Verified.Master boxCompiled.module boxCompiled.tables "sgp4BoxAround"
      boxCompiled.sgp4BoxAround.bound (fun _ => True)
      (fun (x : Float × Float × Float × Float × Float × Float × Float × Float) b =>
        BoxMeets b (valuesOf x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2.1 x.2.2.2.2.2.2.1)
          (value x.2.2.2.2.2.2.2.toBits)) :=
  .of_trapFree boxCompiled.sgp4BoxAround.trapFree
    (Verified.tables_at [0, 1, 2, 3] (by decide) rfl) (by decide +kernel) (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ h => h)
    fun _ _ _ _ _ _ => box_meets ⟨Omm.around_value, Omm.around_value, Omm.around_value, Omm.around_value,
      Omm.around_value, Omm.around_value, Omm.around_value⟩ Omm.around_value

/-- The export `Tle.propagate`, called on two lines of words and an interval of time, returns
status 10 exactly for lines without the layout `WellFormed`, and otherwise a result that meets
`BoxMeets` for the element set that the digits denote and every time in the interval. -/
theorem propagate_master :
    Verified.Master boxCompiled.module boxCompiled.tables "propagate" boxCompiled.propagate.bound
      (fun x => x.1.size < 2 ^ 64 ∧ x.2.1.size < 2 ^ 64)
      (fun (x : Array UInt64 × Array UInt64 × Interval) b =>
        (b.status = 10 ↔ ¬Tle.WellFormed x.1 x.2.1) ∧
          ∀ t', Encloses x.2.2 t' → Tle.WellFormed x.1 x.2.1 →
            BoxMeets b (Tle.elements x.1 x.2.1) t') :=
  .of_trapFree boxCompiled.propagate.trapFree (Verified.tables_at [0, 1, 2, 3] (by decide) rfl)
    (by decide +kernel) (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ _ _ ⟨h1, h2⟩ => Tle.propagate_meets h1 h2

end Demos.Sgp4
