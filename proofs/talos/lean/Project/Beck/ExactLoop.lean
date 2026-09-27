import Project.Beck.ExactRound
import Project.Beck.GenericLoop

namespace Project.Beck.ExactLoop

open LeanExe.Examples.BeckExact ExactState
open LeanExe.Examples.Beck (Input)

structure InputValid (input : Input) : Prop where
  fits : input.jobs ≤ UInt64.size
  binary : ∀ job : Fin input.jobs, ∀ category : Fin input.categories,
    input.incidence[job.val * input.categories + category.val]! = 0 ∨
      input.incidence[job.val * input.categories + category.val]! = 1
  overlap : ∀ job : Fin input.jobs,
    (Finset.univ.filter fun category => job ∈ ExactCounting.members input category).card ≤ input.overlap

theorem allFrozen_eq (point : Point) :
    allFrozen point = ((List.range point.numerators.size).findSome?
      (fun job => if !frozen point job then some false else none)).getD true := by
  let f := fun (job : ℕ) => if !frozen point job then some false else none
  have step (job : ℕ) :
      (if !frozen point job then pure (ForInStep.done (some false, ()))
       else pure (ForInStep.yield (none, ()))) = Basis.searchStep f job (none, ()) := by
    dsimp [Basis.searchStep, f]
    split <;> rfl
  simp only [allFrozen, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp_rw [step]
  change ((forIn (List.range point.numerators.size) (none, ()) (Basis.searchStep f)).run).1.getD true = _
  rw [Basis.forIn_search]
  rfl

theorem allFrozen_iff (point : Point) :
    allFrozen point = true ↔ ∀ job < point.numerators.size, frozen point job = true := by
  rw [allFrozen_eq]
  cases h : (List.range point.numerators.size).findSome?
      (fun job => if !frozen point job then some false else none) with
  | none =>
    have all := List.findSome?_eq_none_iff.mp h
    simpa using all
  | some result =>
    obtain ⟨job, member, found⟩ := List.exists_of_findSome?_eq_some h
    have bound := List.mem_range.mp member
    split at found
    · cases found
      simp_all
      exact ⟨job, bound, by assumption⟩
    · contradiction

theorem live_nonempty (input : Input) (point : Point) (size : point.numerators.size = input.jobs) :
    (ExactCounting.live input point).Nonempty ↔ allFrozen point = false := by
  simp only [Bool.eq_false_iff, ne_eq, allFrozen_iff, size]
  constructor
  · rintro ⟨job, member⟩ all
    have fixed := all job.val job.isLt
    have live := (Finset.mem_filter.mp member).2
    simp [fixed] at live
  · intro missing
    push Not at missing
    obtain ⟨job, bound, flag⟩ := missing
    exact ⟨⟨job, bound⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_false_iff.mpr flag⟩⟩

def step (input : Input) (point : Point) : Point :=
  if allFrozen point then point else (LeanExe.Examples.BeckExact.round input point).getD point

theorem step_correct (input : Input) (inputValid : InputValid input) (point : Point)
    (state : Valid input.jobs point) (nonempty : (ExactCounting.live input point).Nonempty) :
    LeanExe.Examples.BeckExact.round input point = some (step input point) ∧
      Valid input.jobs (step input point) ∧
      (∀ job : Fin input.jobs, frozen point job.val = true → coordinate (step input point) job.val = coordinate point job.val) ∧
      (∃ job : Fin input.jobs, frozen point job.val = false ∧ frozen (step input point) job.val = true) ∧
      (∀ category : Fin input.categories, input.overlap < liveCount input point category.val →
        ∑ job ∈ ExactCounting.members input category, coordinate (step input point) job.val =
          ∑ job ∈ ExactCounting.members input category, coordinate point job.val) := by
  obtain ⟨next, source, nextValid, fixed, progress, preserves⟩ :=
    ExactRound.correct input point inputValid.fits inputValid.binary inputValid.overlap state nonempty
  have equal : step input point = next := by
    simp [step, (live_nonempty input point state.size).mp nonempty, source]
  rw [equal]
  exact ⟨source, nextValid, fixed, progress, preserves⟩

theorem live_eq (input : Input) (point : Point) (state : Valid input.jobs point) :
    GenericLoop.live (fun point (job : Fin input.jobs) => coordinate point job.val) point =
      ExactCounting.live input point := by
  ext job
  simp [GenericLoop.live, ExactCounting.live, interior_iff state job.val job.isLt]

def system (input : Input) (inputValid : InputValid input) :
    GenericLoop.System (Fin input.jobs) (Fin input.categories) Point where
  coordinate point job := coordinate point job.val
  members := ExactCounting.members input
  overlap := input.overlap
  valid := Valid input.jobs
  step := step input
  cube point state job := ExactState.cube state job.val job.isLt
  step_valid point state nonempty :=
    (step_correct input inputValid point state (by rwa [← live_eq input point state])).2.1
  step_fixed point state job outside := by
    by_cases nonempty : (ExactCounting.live input point).Nonempty
    · apply (step_correct input inputValid point state nonempty).2.2.1 job
      rw [live_eq input point state] at outside
      simpa [ExactCounting.live] using outside
    · have done : allFrozen point = true := by
        simpa [live_nonempty input point state.size] using nonempty
      simp [step, done]
  step_progress point state nonempty := by
    rw [live_eq input point state] at nonempty ⊢
    have facts := step_correct input inputValid point state nonempty
    obtain ⟨job, before, after⟩ := facts.2.2.2.1
    refine ⟨job, by simp [ExactCounting.live, before], ?_⟩
    have bound := ExactState.cube facts.2.1 job.val job.isLt
    have endpoint : ¬ |coordinate (step input point) job.val| < 1 := by
      rw [← interior_iff facts.2.1 job.val job.isLt, after]
      decide
    exact le_antisymm bound (le_of_not_gt endpoint)
  step_preserves point state category kept := by
    rw [live_eq input point state, ← ExactCounting.liveCount_card] at kept
    have nonempty : (ExactCounting.live input point).Nonempty := by
      apply Finset.card_pos.mp
      have bound := Finset.card_filter_le (ExactCounting.live input point)
        (fun job => job ∈ ExactCounting.members input category)
      rw [← ExactCounting.liveCount_card] at bound
      omega
    exact (step_correct input inputValid point state nonempty).2.2.2.2 category kept

theorem system_live (input : Input) (inputValid : InputValid input) (point : Point)
    (state : Valid input.jobs point) :
    GenericLoop.live (system input inputValid).coordinate point = ExactCounting.live input point :=
  live_eq input point state

theorem rounds_eq (input : Input) (inputValid : InputValid input) (fuel : ℕ) (point : Point)
    (state : Valid input.jobs point) (enough : (ExactCounting.live input point).card ≤ fuel) :
    rounds fuel input point = some (GenericLoop.rounds (system input inputValid) fuel point) := by
  induction fuel generalizing point with
  | zero =>
    have empty : ¬ (ExactCounting.live input point).Nonempty := by
      intro nonempty
      have positive := nonempty.card_pos
      omega
    have done : allFrozen point = true := by simpa [live_nonempty input point state.size] using empty
    simp [rounds, done, GenericLoop.rounds]
  | succ fuel ih =>
    by_cases nonempty : (ExactCounting.live input point).Nonempty
    · have facts := step_correct input inputValid point state nonempty
      have genericLive : (GenericLoop.live (system input inputValid).coordinate point).Nonempty := by
        rwa [system_live input inputValid point state]
      have fewer := GenericLoop.live_step_lt (system input inputValid) point state genericLive
      change (GenericLoop.live (system input inputValid).coordinate (step input point)).card <
        (GenericLoop.live (system input inputValid).coordinate point).card at fewer
      rw [system_live input inputValid (step input point) facts.2.1,
        system_live input inputValid point state] at fewer
      rw [rounds, (live_nonempty input point state.size).mp nonempty]
      simp only [Bool.false_eq_true, ite_false, facts.1]
      rw [GenericLoop.rounds, ite_eq_left genericLive]
      exact ih _ facts.2.1 (by omega)
    · have done : allFrozen point = true := by simpa [live_nonempty input point state.size] using nonempty
      have genericEmpty : ¬ (GenericLoop.live (system input inputValid).coordinate point).Nonempty := by
        rwa [system_live input inputValid point state]
      simp [rounds, done, GenericLoop.rounds, genericEmpty]

#print axioms rounds_eq

end Project.Beck.ExactLoop
