import Project.Beck.Encoding
import Project.Beck.Result

namespace Project.Beck.Source

open LeanExe.Examples.Beck

def overlap (jobs : List (List Nat)) : Nat := jobs.foldl (fun t ids => max t ids.length) 0

def members (jobs : List (List Nat)) (category : Nat) : Finset (Fin jobs.length) :=
  Finset.univ.filter fun job => category ∈ jobs[job.val]!

theorem matrix_members (categories : Nat) (jobs : List (List Nat)) (category : Fin categories) :
    Counting.members ⟨0, jobs.length, categories, overlap jobs, Encoding.matrix categories jobs⟩ category =
      members jobs category.val := by
  ext job
  simp [Counting.members, members, Encoding.matrix_get categories jobs job.val job.isLt category.val category.isLt,
    show (0 : UInt64) ≠ 1 by decide]

theorem compute_correct (words : Array UInt64) (categories : Nat) (jobs : List (List Nat))
    (encoded : Encoding.Input words categories jobs) :
    (compute words).size = jobs.length + 2 ∧ (compute words)[0]! = 0 ∧
      (compute words)[1]! = (overlap jobs).toUInt64 ∧
      (∀ job < jobs.length, (compute words)[job + 2]! = 0 ∨ (compute words)[job + 2]! = 1) ∧
      ∀ category : Fin categories,
        |(((members jobs category.val).filter fun job => (compute words)[job.val + 2]! = 1).card : ℤ) -
          ((members jobs category.val).filter fun job => (compute words)[job.val + 2]! = 0).card| ≤
          max 0 (2 * (overlap jobs : ℤ) - 1) := by
  have accepted := (Encoding.input_complete words categories jobs encoded).1
  have input := Encoding.input_eq words categories jobs encoded
  have success := Result.compute_success words accepted
  rw [input] at success
  refine ⟨success.1, success.2.1, success.2.2.1, success.2.2.2, ?_⟩
  have bounds := fun category : Fin (readInput words).categories =>
    (Result.compute_discrepancy words accepted category).2.2.2.2
  rw [input] at bounds
  intro category
  have bound := bounds category
  change |(((Counting.members ⟨0, jobs.length, categories, overlap jobs, Encoding.matrix categories jobs⟩ category).filter
    fun job => (compute words)[job.val + 2]! = 1).card : ℤ) -
    ((Counting.members ⟨0, jobs.length, categories, overlap jobs, Encoding.matrix categories jobs⟩ category).filter
    fun job => (compute words)[job.val + 2]! = 0).card| ≤ max 0 (2 * (overlap jobs : ℤ) - 1) at bound
  simpa only [matrix_members] using bound

end Project.Beck.Source
