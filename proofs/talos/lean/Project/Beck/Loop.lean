import Project.Beck.SourceRound

namespace Project.Beck.Loop

open LeanExe.Examples.Beck

theorem allFrozen_eq (x : Point) :
    allFrozen x = ((List.range x.numerators.size).findSome?
      (fun job => if !frozen x job then some false else none)).getD true := by
  let f := fun (job : Nat) => if !frozen x job then some false else none
  have step (job : Nat) :
      (if !frozen x job then pure (ForInStep.done (some false, ()))
       else pure (ForInStep.yield (none, ()))) = Basis.searchStep f job (none, ()) := by
    dsimp [Basis.searchStep, f]
    split <;> rfl
  simp only [allFrozen, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  simp_rw [step]
  change ((forIn (List.range x.numerators.size) (none, ()) (Basis.searchStep f)).run).1.getD true = _
  rw [Basis.forIn_search]
  rfl

theorem allFrozen_iff (x : Point) :
    allFrozen x = true ↔ ∀ job < x.numerators.size, frozen x job = true := by
  rw [allFrozen_eq]
  cases h : (List.range x.numerators.size).findSome?
      (fun job => if !frozen x job then some false else none) with
  | none =>
    have all := List.findSome?_eq_none_iff.mp h
    simpa using all
  | some result =>
    obtain ⟨job, hj, found⟩ := List.exists_of_findSome?_eq_some h
    have bound := List.mem_range.mp hj
    split at found
    · cases found
      simp_all
      exact ⟨job, bound, by assumption⟩
    · contradiction

theorem live_nonempty (input : Input) (x : Point) (size : x.numerators.size = input.jobs) :
    (Counting.live input x).Nonempty ↔ allFrozen x = false := by
  simp only [Bool.eq_false_iff, ne_eq, allFrozen_iff, size]
  constructor
  · rintro ⟨job, member⟩ all
    have frozen := all job.val job.isLt
    have live := (Finset.mem_filter.mp member).2
    simp [frozen] at live
  · intro missing
    push Not at missing
    obtain ⟨job, hj, hf⟩ := missing
    exact ⟨⟨job, hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Bool.eq_false_iff.mpr hf⟩⟩

theorem live_decreases (input : Input) (x : Point) (r : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r) (fuel : r ≤ 5)
    (nonempty : (Counting.live input x).Nonempty) :
    (Counting.live input (LeanExe.Examples.Beck.round input x)).card < (Counting.live input x).card := by
  have step := SourceRound.round_valid_progress input x r supported state fuel nonempty
  have subset : Counting.live input (LeanExe.Examples.Beck.round input x) ⊆ Counting.live input x := by
    intro job member
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Bool.eq_false_iff.mpr
    intro frozen
    have next := step.2.1 job.val job.isLt frozen
    have live := (Finset.mem_filter.mp member).2
    simp [next] at live
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨subset, ?_⟩
  intro equal
  obtain ⟨job, hj, live, frozen⟩ := step.2.2
  have member : (⟨job, hj⟩ : Fin input.jobs) ∈ Counting.live input x := by simp [Counting.live, live]
  rw [← equal] at member
  simp [Counting.live, frozen] at member

theorem rounds_finish (input : Input) (x : Point) (r fuel : Nat)
    (supported : State.Supported input) (state : State.Valid input.jobs x r)
    (budget : r + fuel ≤ 6) (enough : (Counting.live input x).card ≤ fuel) :
    ∃ finalRound ≤ r + fuel, State.Valid input.jobs (rounds fuel input x) finalRound ∧
      allFrozen (rounds fuel input x) = true := by
  induction fuel generalizing r x with
  | zero =>
    have done : allFrozen x = true := by
      cases h : allFrozen x
      · have nonempty := (live_nonempty input x state.size).mpr h
        have := nonempty.card_pos
        omega
      · rfl
    refine ⟨r, by omega, ?_, ?_⟩
    · simpa [rounds, done] using state
    · simp [rounds, done]
  | succ fuel ih =>
    by_cases done : allFrozen x = true
    · refine ⟨r, by omega, ?_, ?_⟩
      · simpa [rounds, done] using state
      · simp [rounds, done]
    · have running : allFrozen x = false := Bool.eq_false_iff.mpr done
      have nonempty := (live_nonempty input x state.size).mpr running
      have limit : r ≤ 5 := by omega
      have next := (SourceRound.round_valid_progress input x r supported state limit nonempty).1
      have fewer := live_decreases input x r supported state limit nonempty
      have nonzero : (LeanExe.Examples.Beck.round input x).denominator ≠ 0 := by
        intro zero
        have positive := next.positive
        simp [zero] at positive
      obtain ⟨finalRound, bound, valid, finished⟩ := ih (LeanExe.Examples.Beck.round input x) (r + 1)
        next (by omega) (by omega)
      refine ⟨finalRound, by omega, ?_, ?_⟩
      · simpa [rounds, done, nonzero] using valid
      · simpa [rounds, done, nonzero] using finished

theorem initial_finishes (input : Input) (supported : State.Supported input) :
    let result := rounds input.jobs input ⟨1, Array.replicate input.jobs 0⟩
    result.denominator ≠ 0 ∧ result.numerators.size = input.jobs ∧ allFrozen result = true ∧
      result.denominator.toNat ≤ 120 ^ 6 := by
  have liveBound : (Counting.live input ⟨1, Array.replicate input.jobs 0⟩).card ≤ input.jobs :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  obtain ⟨r, bound, valid, finished⟩ := rounds_finish input _ 0 input.jobs supported
    (State.initial input.jobs) (by simpa using supported.capacity) liveBound
  dsimp only
  refine ⟨?_, valid.size, finished, ?_⟩
  · intro zero
    have positive := valid.positive
    simp [zero] at positive
  · exact valid.denominator.trans (Nat.pow_le_pow_right (by decide)
      ((by simpa using bound : r ≤ input.jobs).trans supported.capacity))

end Project.Beck.Loop
