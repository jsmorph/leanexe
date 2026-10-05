import Project.Drone.Sqrt
import Project.Drone.Optimality

/-! The loop over the sources in `best` keeps the best candidate, the lowest source among
equals, and a row built by `LeanExe.build` holds `best` of each target. -/

namespace Project.Drone

open LeanExe.Examples.Drone Optimality
open Project.IR (loop_induction build_size build_get)

/-- One step of the loop over the sources in `best`. -/
def bestStep (r0 r1 : UInt64) (table : Array Choice) (base target source : UInt64)
    (acc : UInt64 × UInt64 × UInt64) : UInt64 × UInt64 × UInt64 :=
  let c := choose ⟨acc.1, acc.2.1, acc.2.2⟩
    (predecessor r0 r1 table[(base + source).toNat]! target source)
  (c.time, c.excess, c.parent)

theorem best_loop (r0 r1 : UInt64) (table : Array Choice) (base target sources : UInt64) :
    best r0 r1 table base target sources =
      ⟨(LeanExe.loop sources (infinity, infinity, 0) (bestStep r0 r1 table base target)).1,
        (LeanExe.loop sources (infinity, infinity, 0) (bestStep r0 r1 table base target)).2.1,
        (LeanExe.loop sources (infinity, infinity, 0) (bestStep r0 r1 table base target)).2.2⟩ := by
  unfold best bestStep
  rfl

/-- The number of sources of target `target` in a row: all 45, except at the last station,
which admits only state 0. -/
def sourceCount (last : Bool) (target : UInt64) : UInt64 :=
  if (!last || target == 0) = true then 45 else 0

theorem advance_build (r0 r1 : UInt64) (last : Bool) (table : Array Choice) (base : UInt64) :
    advance r0 r1 last table base =
      LeanExe.build 45 fun target => best r0 r1 table base target (sourceCount last target) :=
  rfl

theorem advance_size (r0 r1 : UInt64) (last : Bool) (table : Array Choice) (base : UInt64) :
    (advance r0 r1 last table base).size = 45 := by
  rw [advance_build, build_size]
  rfl

theorem advance_get (r0 r1 : UInt64) (last : Bool) (table : Array Choice) (base target : UInt64)
    (ht : target.toNat < 45) :
    (advance r0 r1 last table base)[target.toNat]! =
      best r0 r1 table base target (sourceCount last target) := by
  rw [advance_build, build_get ht, UInt64.ofNat_toNat]

namespace Selection

def cost (choice : Choice) : Cost := ⟨choice.time.toNat, choice.excess.toNat⟩

theorem choose_eq (a b : Choice) :
    choose a b = if b.time < a.time ∨ b.time = a.time ∧ b.excess < a.excess then b else a := by
  simp [choose]

theorem choose_left (a b : Choice) : (cost (choose a b)).LE (cost a) := by
  rw [choose_eq]
  split <;> rename_i h
  · dsimp [cost, Cost.LE]
    simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at h
    omega
  · exact Cost.le_refl _

theorem choose_right (a b : Choice) : (cost (choose a b)).LE (cost b) := by
  rw [choose_eq]
  split <;> rename_i h
  · exact Cost.le_refl _
  · dsimp [cost, Cost.LE]
    simp only [UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj] at h
    omega

theorem choose_attained (a b : Choice) : choose a b = a ∨ choose a b = b := by
  rw [choose_eq]
  split <;> simp

/-- The candidate through `source`. -/
abbrev candidate (r0 r1 : UInt64) (table : Array Choice) (base target source : UInt64) :
    Choice :=
  predecessor r0 r1 table[(base + source).toNat]! target source

/-- The choice the loop holds after its first `k` sources. -/
def Scanned (r0 r1 : UInt64) (table : Array Choice) (base target : UInt64) (k : Nat)
    (acc : UInt64 × UInt64 × UInt64) : Prop :=
  let c : Choice := ⟨acc.1, acc.2.1, acc.2.2⟩
  (cost c).LE (cost unreachable) ∧
  (∀ source : UInt64, source.toNat < k →
    (cost c).LE (cost (candidate r0 r1 table base target source))) ∧
  (c = unreachable ∨ ∃ source : UInt64, source.toNat < k ∧
    c = candidate r0 r1 table base target source)

theorem scanned (r0 r1 : UInt64) (table : Array Choice) (base target sources : UInt64) :
    Scanned r0 r1 table base target sources.toNat
      (LeanExe.loop sources (infinity, infinity, 0) (bestStep r0 r1 table base target)) := by
  refine loop_induction _ ⟨Cost.le_refl _, fun s hs => absurd hs (Nat.not_lt_zero _),
    Or.inl rfl⟩ ?_
  rintro k ⟨t, e, p⟩ hk ⟨hle, hmin, hatt⟩
  have hkn : (UInt64.ofNat k).toNat = k :=
    UInt64.toNat_ofNat_of_lt' (lt_of_lt_of_le hk (Nat.le_of_lt (UInt64.toNat_lt_size _)))
  let c : Choice := ⟨t, e, p⟩
  let q := candidate r0 r1 table base target (UInt64.ofNat k)
  have hstep : (⟨(bestStep r0 r1 table base target (UInt64.ofNat k) (t, e, p)).1,
      (bestStep r0 r1 table base target (UInt64.ofNat k) (t, e, p)).2.1,
      (bestStep r0 r1 table base target (UInt64.ofNat k) (t, e, p)).2.2⟩ : Choice) =
      choose c q := rfl
  simp only [Scanned]
  rw [hstep]
  refine ⟨Cost.le_trans (choose_left c q) hle, fun s hs => ?_, ?_⟩
  · by_cases hsk : s.toNat = k
    · have : s = UInt64.ofNat k := by
        apply UInt64.toNat_inj.mp; rw [hkn, hsk]
      subst this
      exact choose_right c q
    · exact Cost.le_trans (choose_left c q) (hmin s (by omega))
  · rcases choose_attained c q with h | h
    · rw [h]
      rcases hatt with h' | ⟨s, hs, h'⟩
      · exact Or.inl h'
      · exact Or.inr ⟨s, by omega, h'⟩
    · exact Or.inr ⟨UInt64.ofNat k, by omega, h⟩

theorem best_scanned (r0 r1 : UInt64) (table : Array Choice) (base target sources : UInt64) :
    (cost (best r0 r1 table base target sources)).LE (cost unreachable) ∧
    (∀ source : UInt64, source.toNat < sources.toNat →
      (cost (best r0 r1 table base target sources)).LE
        (cost (candidate r0 r1 table base target source))) ∧
    (best r0 r1 table base target sources = unreachable ∨
      ∃ source : UInt64, source.toNat < sources.toNat ∧
        best r0 r1 table base target sources = candidate r0 r1 table base target source) := by
  rw [best_loop]
  exact scanned r0 r1 table base target sources

/-- `best` is no worse than the candidate through any of its sources. -/
theorem scan_minimum (r0 r1 : UInt64) (table : Array Choice) (base target sources source : UInt64)
    (hs : source.toNat < sources.toNat) :
    (cost (best r0 r1 table base target sources)).LE
      (cost (predecessor r0 r1 table[(base + source).toNat]! target source)) :=
  (best_scanned r0 r1 table base target sources).2.1 source hs

/-- A finite `best` is the candidate through one of its sources, whose previous choice is finite
and whose edge is admitted. -/
theorem finite_best (r0 r1 : UInt64) (table : Array Choice) (base target sources : UInt64)
    (hfinite : (best r0 r1 table base target sources).time < infinity) :
    ∃ source : UInt64, source.toNat < sources.toNat ∧
      table[(base + source).toNat]!.time < infinity ∧
      0 < edgeTicks r0 r1 (altitude r0 source) (altitude r1 target) (speed source)
        (speed target) ∧
      best r0 r1 table base target sources =
        predecessor r0 r1 table[(base + source).toNat]! target source := by
  rcases (best_scanned r0 r1 table base target sources).2.2 with hu | ⟨source, hs, heq⟩
  · rw [hu] at hfinite
    simp at hfinite
  · have hp : predecessor r0 r1 table[(base + source).toNat]! target source ≠ unreachable := by
      intro h
      rw [heq, candidate, h] at hfinite
      simp at hfinite
    unfold predecessor at hp
    simp only at hp
    split at hp
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨source, hs, h.1, h.2, heq⟩
    · exact absurd rfl hp

end Selection

end Project.Drone
