import LeanExe.Examples.Drone
import Project.Drone.Optimality

namespace Project.Drone.Selection
open LeanExe.Examples.Drone Optimality

def cost (choice : Choice) : Cost := ⟨choice.time.toNat, choice.excess.toNat⟩

theorem choose_left (a b : Choice) : (cost (choose a b)).LE (cost a) := by
  unfold choose
  split <;> rename_i h
  · dsimp [cost, Cost.LE]
    simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at h
    omega
  · exact Cost.le_refl _

theorem choose_right (a b : Choice) : (cost (choose a b)).LE (cost b) := by
  unfold choose
  split <;> rename_i h
  · exact Cost.le_refl _
  · dsimp [cost, Cost.LE]
    simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at h
    omega

theorem choose_attained (a b : Choice) : choose a b = a ∨ choose a b = b := by
  unfold choose
  split <;> simp

/-- The executable tail-recursive scan can only improve its accumulator. -/
theorem scan_le_initial (count start : Nat) (r0 r1 : UInt64)
    (previous : Array UInt64) (target : Nat) (initial : Choice) :
    (cost (scanPredecessors count start r0 r1 previous target initial)).LE (cost initial) := by
  induction count generalizing start initial with
  | zero => exact Cost.le_refl _
  | succ count ih =>
    exact Cost.le_trans (ih _ _) (choose_left _ _)

/-- The actual executable scan dominates every candidate in its interval. -/
theorem scan_interval_minimum (count start : Nat) (r0 r1 : UInt64)
    (previous : Array UInt64) (target source : Nat) (initial : Choice)
    (hs0 : start ≤ source) (hs1 : source < start+count) :
    (cost (scanPredecessors count start r0 r1 previous target initial)).LE
      (cost (predecessor r0 r1 previous target source)) := by
  induction count generalizing start initial with
  | zero => omega
  | succ count ih =>
    rw [scanPredecessors]
    by_cases heq : source = start
    · subst source
      exact Cost.le_trans (scan_le_initial _ _ _ _ _ _ _) (choose_right _ _)
    · exact ih _ _ (by omega) (by omega)

theorem scan_minimum (count : Nat) (r0 r1 : UInt64) (previous : Array UInt64)
    (target source : Nat) (hs : source < count) :
    (cost (bestPredecessor count r0 r1 previous target)).LE
      (cost (predecessor r0 r1 previous target source)) :=
  scan_interval_minimum count 0 r0 r1 previous target source unreachable (by omega) (by omega)

theorem scan_le_unreachable (count : Nat) (r0 r1 : UInt64)
    (previous : Array UInt64) (target : Nat) :
    (cost (bestPredecessor count r0 r1 previous target)).LE (cost unreachable) :=
  scan_le_initial count 0 r0 r1 previous target unreachable

/-- Selection returns the accumulator or an actual candidate in the interval. -/
theorem scan_interval_attained (count start : Nat) (r0 r1 : UInt64)
    (previous : Array UInt64) (target : Nat) (initial : Choice) :
    scanPredecessors count start r0 r1 previous target initial = initial ∨
    ∃ source, start ≤ source ∧ source < start+count ∧
      scanPredecessors count start r0 r1 previous target initial =
        predecessor r0 r1 previous target source := by
  induction count generalizing start initial with
  | zero => exact Or.inl rfl
  | succ count ih =>
    rw [scanPredecessors]
    rcases ih (start+1) (choose initial (predecessor r0 r1 previous target start))
      with h | ⟨source, hs0, hs1, heq⟩
    · rw [h]
      rcases choose_attained initial (predecessor r0 r1 previous target start) with ha | hb
      · exact Or.inl ha
      · exact Or.inr ⟨start, by omega, by omega, hb⟩
    · exact Or.inr ⟨source, by omega, by omega, heq⟩

theorem scan_attained (count : Nat) (r0 r1 : UInt64) (previous : Array UInt64)
    (target : Nat) :
    bestPredecessor count r0 r1 previous target = unreachable ∨
    ∃ source, source < count ∧ bestPredecessor count r0 r1 previous target =
      predecessor r0 r1 previous target source := by
  rcases scan_interval_attained count 0 r0 r1 previous target unreachable with h | ⟨i, _, hi, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨i, by omega, h⟩

theorem finite_scan_predecessor (count : Nat) (r0 r1 : UInt64)
    (previous : Array UInt64) (target : Nat)
    (hfinite : (bestPredecessor count r0 r1 previous target).time < infinity) :
    ∃ source, source < count ∧
      previous[3*source]! < infinity ∧
      0 < edgeTicks r0 r1 (altitude r0 source) (altitude r1 target)
        (speed source) (speed target) ∧
      bestPredecessor count r0 r1 previous target =
        predecessor r0 r1 previous target source := by
  rcases scan_attained count r0 r1 previous target with hu | ⟨source, hs, heq⟩
  · rw [hu] at hfinite
    simp [unreachable] at hfinite
  · refine ⟨source, hs, ?_, ?_, heq⟩
    all_goals
      have hp : predecessor r0 r1 previous target source ≠ unreachable := by
        intro h
        rw [heq, h] at hfinite
        simp [unreachable] at hfinite
      unfold predecessor at hp
      dsimp only at hp
      split at hp
      · rename_i h
        first | exact h.1 | exact h.2
      · exact False.elim (hp rfl)

/-- Packed DP rows always have exactly three words per completed state. -/
theorem advanceLoop_size (count target : Nat) (r0 r1 : UInt64) (last : Bool)
    (previous row : Array UInt64) :
    (advanceLoop count target r0 r1 last previous row).size = row.size+3*count := by
  induction count generalizing target row with
  | zero => simp [advanceLoop]
  | succ count ih =>
    simp only [advanceLoop, ih, Array.size_push]
    omega

theorem advance_size (r0 r1 : UInt64) (last : Bool) (previous : Array UInt64) :
    (advance r0 r1 last previous).size = 135 := by
  simp [advance, advanceLoop_size, stateCount]

#print axioms scan_minimum
#print axioms finite_scan_predecessor
end Project.Drone.Selection
