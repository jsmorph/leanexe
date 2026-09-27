import Project.Beck.ExactEncoding
import Project.Beck.ExactResult

namespace Project.Beck.ExactSource

open LeanExe.Examples.BeckExact

def overlap (jobs : List (List ℕ)) : ℕ := jobs.foldl (fun t ids => max t ids.length) 0

def members (jobs : List (List ℕ)) (category : ℕ) : Finset (Fin jobs.length) :=
  Finset.univ.filter fun job => category ∈ jobs[job.val]!

theorem matrix_members (categories : ℕ) (jobs : List (List ℕ)) (category : Fin categories) :
    ExactCounting.members ⟨0, jobs.length, categories, overlap jobs, Encoding.matrix categories jobs⟩ category =
      members jobs category.val := by
  ext job
  simp [ExactCounting.members, members, Encoding.matrix_get categories jobs job.val job.isLt category.val category.isLt,
    show (0 : UInt64) ≠ 1 by decide]

theorem compute_correct (words : Array UInt64) (categories : ℕ) (jobs : List (List ℕ))
    (encoded : ExactEncoding.Input words categories jobs) :
    (compute words).size = jobs.length + 2 ∧ (compute words)[0]! = 0 ∧
      (compute words)[1]! = (overlap jobs).toUInt64 ∧
      (∀ job < jobs.length, (compute words)[job + 2]! = 0 ∨ (compute words)[job + 2]! = 1) ∧
      ∀ category : Fin categories,
        |(((members jobs category.val).filter fun job => (compute words)[job.val + 2]! = 1).card : ℤ) -
          ((members jobs category.val).filter fun job => (compute words)[job.val + 2]! = 0).card| ≤
          max 0 (2 * (overlap jobs : ℤ) - 1) := by
  have input := ExactEncoding.input_complete words categories jobs encoded
  change readInput words = ⟨0, jobs.length, categories, overlap jobs, Encoding.matrix categories jobs⟩ at input
  have accepted : (readInput words).status = 0 := by rw [input]
  have correct := ExactResult.compute_correct words accepted
  rw [input] at correct
  refine ⟨correct.1, correct.2.1, correct.2.2.1, correct.2.2.2.1, ?_⟩
  intro category
  simpa only [matrix_members] using correct.2.2.2.2 category

#print axioms compute_correct

end Project.Beck.ExactSource
