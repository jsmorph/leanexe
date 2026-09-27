import Project.Beck.ExactDirection

namespace Project.Beck.ExactState

open LeanExe.Examples.BeckExact
open IntegerAdd (value)

structure Valid (jobs : ℕ) (point : Point) : Prop where
  size : point.numerators.size = jobs
  numerators : ∀ entry ∈ point.numerators, IntegerAdd.Valid entry
  denominator : IntegerAdd.Valid point.denominator
  positive : 0 < value point.denominator
  cube : ∀ job, job < jobs → |value point.numerators[job]!| ≤ value point.denominator

def coordinate (point : Point) (job : ℕ) : ℚ :=
  (value point.numerators[job]! : ℚ) / (value point.denominator : ℚ)

theorem numerator_valid {jobs : ℕ} {point : Point} (valid : Valid jobs point)
    (job : ℕ) (inside : job < jobs) : IntegerAdd.Valid point.numerators[job]! :=
  Elimination.get_valid _ valid.numerators job (by rw [valid.size]; exact inside)

theorem frozen_iff {jobs : ℕ} {point : Point} (valid : Valid jobs point)
    (job : ℕ) (inside : job < jobs) :
    frozen point job = true ↔ |value point.numerators[job]!| = value point.denominator := by
  have absolute := IntegerOrder.abs_correct _ (numerator_valid valid job inside)
  rw [frozen, IntegerOrder.equal_correct _ _ absolute.1 valid.denominator, absolute.2]

theorem live_iff {jobs : ℕ} {point : Point} (valid : Valid jobs point)
    (job : ℕ) (inside : job < jobs) :
    frozen point job = false ↔ |value point.numerators[job]!| < value point.denominator := by
  have bound := valid.cube job inside
  rw [← Bool.not_eq_true, frozen_iff valid job inside]
  omega

theorem cube {jobs : ℕ} {point : Point} (valid : Valid jobs point)
    (job : ℕ) (inside : job < jobs) : |coordinate point job| ≤ 1 := by
  have positive : (0 : ℚ) < value point.denominator := by exact_mod_cast valid.positive
  rw [coordinate, abs_div, abs_of_pos positive, div_le_one positive]
  exact_mod_cast valid.cube job inside

theorem interior_iff {jobs : ℕ} {point : Point} (valid : Valid jobs point)
    (job : ℕ) (inside : job < jobs) :
    frozen point job = false ↔ |coordinate point job| < 1 := by
  have positive : (0 : ℚ) < value point.denominator := by exact_mod_cast valid.positive
  rw [live_iff valid job inside, coordinate, abs_div, abs_of_pos positive, div_lt_one positive]
  exact_mod_cast Iff.rfl

theorem negative_iff (integer : Integer) (valid : IntegerAdd.Valid integer) :
    integer.negative = true ↔ value integer < 0 := by
  have normalized := valid.2
  cases sign : integer.negative <;> simp_all [IntegerAdd.value] <;> omega

theorem initial (jobs : ℕ) : Valid jobs ⟨Integer.ofWord 1, Array.replicate jobs Integer.zero⟩ := by
  have one := IntegerOrder.ofWord_correct 1
  refine ⟨by simp, ?_, one.1, by simp [one.2], ?_⟩
  · intro entry member
    have equal := Array.eq_of_mem_replicate member
    simpa [equal] using IntegerAdd.zero_correct.1
  · intro job inside
    simp [getElem!_pos (Array.replicate jobs Integer.zero) job (by simpa using inside),
      IntegerAdd.zero_correct.2, one.2]

#print axioms interior_iff
#print axioms initial

end Project.Beck.ExactState
