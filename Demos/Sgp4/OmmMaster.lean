import Demos.Sgp4.OmmVerified
import Demos.Sgp4.OmmSound
import Verified.Master

/-!
The master theorems of the exports `field` and `fieldNonneg` of the module `sgp4omm`, the readers
of the decimal values of an Orbit Mean-Elements Message.
-/

namespace Demos.Sgp4.Omm

open Library.Numerics.Interval Library.Numerics.Decimal.Shared.StrconvGrammar

/-- What a reader of a value states of the text `text` and its interval `i`: for every byte list
`s` of fewer than `2 ^ 32` bytes whose words are `text`, the interval of a number of the general
grammar of `parse64` contains the number, an infinity or a NaN has a rejected interval, and so
does a text outside the grammar. -/
def Reads (text : Array UInt64) (i : Interval) : Prop :=
  ∀ s : List UInt8, words s = text → s.length < 2 ^ 32 →
    (∀ n, Derives true s n →
      (∀ x, numValue n = some x → Encloses i x) ∧ (numValue n = none → i.status ≠ 0)) ∧
    ((∀ n, ¬Derives true s n) → i.status = 1)

/-- The export `field` reads a decimal or hexadecimal value as an interval that contains it. -/
theorem field_master :
    Verified.Master compiled.module compiled.tables "field" compiled.field.bound (fun _ => True)
      Reads :=
  .of_trapFree (.ofA compiled.field.trapFree) nofun (by decide +kernel)
    (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ text _ _ s hs hlen => by
      subst hs
      exact ⟨fun n h => field_sound s hlen h, field_rejects s hlen⟩

/-- The export `fieldNonneg` reads a value as an interval that contains it, clamped at 0 when the
text has no leading `-`. -/
theorem fieldNonneg_master :
    Verified.Master compiled.module compiled.tables "fieldNonneg" compiled.fieldNonneg.bound
      (fun _ => True)
      (fun text i => ∀ s : List UInt8, words s = text → s.length < 2 ^ 32 →
        ∀ n, Derives true s n → ∀ x, numValue n = some x → Encloses i x) :=
  .of_trapFree (.ofA compiled.fieldNonneg.trapFree) nofun (by decide +kernel) (fun _ _ _ _ h => h) (fun _ _ _ _ _ h => h)
    fun _ _ _ text _ _ s hs hlen n h x hx => by
      subst hs
      exact fieldNonneg_encloses s hlen h hx

#print axioms field_master
#print axioms fieldNonneg_master

end Demos.Sgp4.Omm
