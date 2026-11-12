import LeanExe.Dialect.Lemmas
import LeanExe.Dialect.ArrayLemmas

/-!
Loops that build an array from the cells of another.  Each step appends to the accumulator, so
the accumulator stays a prefix of the result.  `loop_cover` states that every element of the
result has a property that each step gives the elements it appends, and that a cell with a
property `In` leaves an element with a property `Out` in the result when each step that reads such
a cell appends or keeps one.  The searches of the screening program are loops of this form.
-/

namespace Demos.Screening

open LeanExe.Dialect

/-- A step keeps the accumulator as a prefix of its result. -/
def Extends {D : Type} [Inhabited D] (f : Array D → Array D) : Prop :=
  ∀ acc, acc.size ≤ (f acc).size ∧ ∀ j < acc.size, (f acc)[j]! = acc[j]!

theorem extends_id {D : Type} [Inhabited D] : Extends (fun acc : Array D => acc) :=
  fun _ => ⟨le_rfl, fun _ _ => rfl⟩

theorem extends_push {D : Type} [Inhabited D] {f : Array D → Array D} (hf : Extends f) (x : D) :
    Extends (fun acc => (f acc).push x) := fun acc => by
  obtain ⟨h1, h2⟩ := hf acc
  refine ⟨by simp only [Array.size_push]; omega, fun j hj => ?_⟩
  rw [push_get_lt _ _ (by omega)]
  exact h2 j hj

theorem extends_ite {D : Type} [Inhabited D] {f g : Array D → Array D} (c : Prop) [Decidable c]
    (hf : Extends f) (hg : Extends g) : Extends (fun acc => if c then f acc else g acc) := by
  by_cases h : c
  · simpa [h] using hf
  · simpa [h] using hg

/-- The loop over the cells. -/
theorem loop_cover {C D : Type} [Inhabited C] [Inhabited D] (cells : Array C)
    (h64 : cells.size < 2 ^ 64) (step : C → Array D → Array D) (hext : ∀ c, Extends (step c))
    (Keep : D → Prop)
    (hkeep : ∀ i < cells.size, ∀ acc j, acc.size ≤ j → j < (step cells[i]! acc).size →
      Keep (step cells[i]! acc)[j]!)
    (In : C → Prop) (Out : D → Prop)
    (hcov : ∀ i < cells.size, In cells[i]! → ∀ acc : Array D,
      ∃ j < (step cells[i]! acc).size, Out (step cells[i]! acc)[j]!) :
    (∀ j < (LeanExe.loop cells.size.toUInt64 #[] fun i acc => step cells[i.toNat]! acc).size,
        Keep (LeanExe.loop cells.size.toUInt64 #[] fun i acc => step cells[i.toNat]! acc)[j]!) ∧
      ((∃ i < cells.size, In cells[i]!) →
        ∃ j < (LeanExe.loop cells.size.toUInt64 #[] fun i acc => step cells[i.toNat]! acc).size,
          Out (LeanExe.loop cells.size.toUInt64 #[] fun i acc =>
            step cells[i.toNat]! acc)[j]!) := by
  have hn := size_toUInt64 cells h64
  have key := loop_induction (n := cells.size.toUInt64) (init := (#[] : Array D))
    (f := fun i acc => step cells[i.toNat]! acc)
    (fun k acc => (∀ j < acc.size, Keep acc[j]!) ∧
      ∀ i < k, In cells[i]! → ∃ j < acc.size, Out acc[j]!)
    ⟨fun j hj => absurd hj (by simp), fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    (fun k acc hk ⟨hK, hC⟩ => by
      rw [hn] at hk
      have hk' : (UInt64.ofNat k).toNat = k := by
        rw [UInt64.toNat_ofNat']; omega
      simp only [hk']
      obtain ⟨hs, hp⟩ := hext cells[k]! acc
      refine ⟨fun j hj => ?_, fun i hi hin => ?_⟩
      · by_cases hjs : j < acc.size
        · rw [hp j hjs]; exact hK j hjs
        · exact hkeep k hk acc j (by omega) hj
      · by_cases hik : i < k
        · obtain ⟨j, hj, ho⟩ := hC i hik hin
          exact ⟨j, by omega, by rw [hp j hj]; exact ho⟩
        · have : i = k := by omega
          subst this
          exact hcov i hk hin acc)
  rw [hn] at key
  exact ⟨key.1, fun ⟨i, hi, hin⟩ => key.2 i hi hin⟩

/-- A loop whose step appends at most `w` elements builds at most `w` elements for each cell. -/
theorem loop_size_le {C D : Type} [Inhabited C] (cells : Array C) (h64 : cells.size < 2 ^ 64)
    {w : Nat} (step : C → Array D → Array D) (hs : ∀ c acc, (step c acc).size ≤ acc.size + w) :
    (LeanExe.loop cells.size.toUInt64 #[] fun i acc => step cells[i.toNat]! acc).size ≤
      w * cells.size := by
  have hn := size_toUInt64 cells h64
  have key := loop_induction (n := cells.size.toUInt64) (init := (#[] : Array D))
    (f := fun i acc => step cells[i.toNat]! acc) (fun k acc => acc.size ≤ w * k) (by simp)
    (fun k acc _ ih => by
      have := hs cells[(UInt64.ofNat k).toNat]! acc
      rw [Nat.mul_succ]
      omega)
  rw [hn] at key
  exact key

end Demos.Screening
