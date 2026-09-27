import Project.Beck.ExactLoop

namespace Project.Beck.ExactFinish

open LeanExe.Examples.BeckExact ExactState ExactLoop
open LeanExe.Examples.Beck (Input)

def initial (jobs : ℕ) : Point := ⟨Integer.ofWord 1, Array.replicate jobs Integer.zero⟩

def sign (point : Point) (job : ℕ) : ℤ := if point.numerators[job]!.negative then -1 else 1

theorem sign_eq (input : Input) (inputValid : InputValid input) (point : Point)
    (state : Valid input.jobs point) (job : Fin input.jobs) :
    GenericLoop.sign (system input inputValid) point job = sign point job.val := by
  have positive : (0 : ℚ) < IntegerAdd.value point.denominator := by exact_mod_cast state.positive
  have negative : coordinate point job.val < 0 ↔ IntegerAdd.value point.numerators[job.val]! < 0 := by
    rw [coordinate, div_lt_iff₀ positive, zero_mul]
    exact_mod_cast Iff.rfl
  change (if coordinate point job.val < 0 then (-1 : ℤ) else 1) = _
  simp only [negative, ← negative_iff _ (numerator_valid state job.val job.isLt), sign]

theorem initial_correct (input : Input) (inputValid : InputValid input) :
    ∃ result, rounds input.jobs input (initial input.jobs) = some result ∧
      Valid input.jobs result ∧ allFrozen result = true ∧
      (∀ job : Fin input.jobs, coordinate result job.val = -1 ∨ coordinate result job.val = 1) ∧
      ∀ category : Fin input.categories,
        |∑ job ∈ ExactCounting.members input category, sign result job.val| ≤
          max 0 (2 * (input.overlap : ℤ) - 1) := by
  let sys := system input inputValid
  let result := GenericLoop.rounds sys input.jobs (initial input.jobs)
  have initialValid : Valid input.jobs (initial input.jobs) := ExactState.initial input.jobs
  have enough : (ExactCounting.live input (initial input.jobs)).card ≤ input.jobs :=
    (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)
  have source := rounds_eq input inputValid input.jobs (initial input.jobs) initialValid enough
  have valid : Valid input.jobs result := GenericLoop.rounds_valid sys input.jobs _ initialValid
  have finished : ExactCounting.live input result = ∅ := by
    rw [← system_live input inputValid result valid]
    apply GenericLoop.rounds_finish sys input.jobs _ initialValid
    rwa [system_live input inputValid _ initialValid]
  have correct := GenericLoop.initial_correct sys (initial input.jobs) initialValid (by
    intro job
    change coordinate (initial input.jobs) job.val = 0
    simp [coordinate, initial, IntegerAdd.zero_correct.2]) inputValid.overlap
  simp only [Fintype.card_fin] at correct
  refine ⟨result, source, valid, ?_, correct.1, ?_⟩
  · have empty : ¬ (ExactCounting.live input result).Nonempty := by simp [finished]
    simpa [live_nonempty input result valid.size] using empty
  · intro category
    have bound := correct.2 category
    change |∑ job ∈ ExactCounting.members input category, GenericLoop.sign (system input inputValid) result job| ≤
      max 0 (2 * (input.overlap : ℤ) - 1) at bound
    simpa only [sign_eq input inputValid result valid] using bound

#print axioms initial_correct

end Project.Beck.ExactFinish
