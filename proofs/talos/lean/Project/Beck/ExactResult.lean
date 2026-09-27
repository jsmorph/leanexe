import Project.Beck.ExactFinish
import Project.Beck.ExactParser

namespace Project.Beck.ExactResult

open LeanExe.Examples.BeckExact
open LeanExe.Examples.Beck (Input)

def group (point : Point) (job : ℕ) : UInt64 := if point.numerators[job]!.negative then 0 else 1

def output (input : Input) (point : Point) : Array UInt64 :=
  #[0, input.overlap.toUInt64] ++ ((List.range input.jobs).map (group point)).toArray

theorem compute_eq (words : Array UInt64) (accepted : (readInput words).status = 0)
    (result : Point) (finished : rounds (readInput words).jobs (readInput words)
      (ExactFinish.initial (readInput words).jobs) = some result) :
    compute words = output (readInput words) result := by
  simp only [compute, accepted, bne_self_eq_false, Bool.false_eq_true, ite_false]
  change (match rounds (readInput words).jobs (readInput words)
    (ExactFinish.initial (readInput words).jobs) with | none => _ | some result => _) = _
  rw [finished]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', bind, pure]
  have loop := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range (readInput words).jobs)
    (fun job (acc : Array UInt64) => acc.push (group result job)) #[0, (readInput words).overlap.toUInt64]
  exact loop.trans (by simp [pure, output])

theorem output_size (input : Input) (point : Point) : (output input point).size = input.jobs + 2 := by
  simp [output]

theorem output_group (input : Input) (point : Point) (job : ℕ) (inside : job < input.jobs) :
    (output input point)[job + 2]! = group point job := by
  have bound : job + 2 < (output input point).size := by rw [output_size]; omega
  rw [getElem!_pos (output input point) (job + 2) bound]
  simp only [output]
  rw [Array.getElem_append_right (by change 2 ≤ job + 2; omega)]
  simp

theorem sign_count (input : Input) (point : Point) (category : Fin input.categories) :
    (∑ job ∈ ExactCounting.members input category, ExactFinish.sign point job.val) =
      (((ExactCounting.members input category).filter fun job => group point job.val = 1).card : ℤ) -
        ((ExactCounting.members input category).filter fun job => group point job.val = 0).card := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro job _
  unfold ExactFinish.sign group
  split <;> norm_num [show (0 : UInt64) ≠ 1 by decide, show (1 : UInt64) ≠ 0 by decide]

theorem compute_correct (words : Array UInt64) (accepted : (readInput words).status = 0) :
    (compute words).size = (readInput words).jobs + 2 ∧ (compute words)[0]! = 0 ∧
      (compute words)[1]! = (readInput words).overlap.toUInt64 ∧
      (∀ job < (readInput words).jobs, (compute words)[job + 2]! = 0 ∨ (compute words)[job + 2]! = 1) ∧
      ∀ category : Fin (readInput words).categories,
        |(((ExactCounting.members (readInput words) category).filter fun job =>
            (compute words)[job.val + 2]! = 1).card : ℤ) -
          ((ExactCounting.members (readInput words) category).filter fun job =>
            (compute words)[job.val + 2]! = 0).card| ≤
          max 0 (2 * ((readInput words).overlap : ℤ) - 1) := by
  obtain ⟨result, finished, _, _, _, bounds⟩ :=
    ExactFinish.initial_correct (readInput words) (ExactParser.accepted_input words accepted)
  rw [compute_eq words accepted result finished]
  refine ⟨output_size _ _, by simp [output], by simp [output], ?_, ?_⟩
  · intro job inside
    rw [output_group _ _ job inside]
    unfold group
    split <;> simp
  · intro category
    simp_rw [output_group (readInput words) result _ (Fin.isLt _)]
    rw [← sign_count]
    exact bounds category

theorem compute_rejected (words : Array UInt64) (rejected : (readInput words).status ≠ 0) :
    compute words = #[(readInput words).status] := by
  simp [compute, rejected]

#print axioms compute_correct
#print axioms compute_rejected

end Project.Beck.ExactResult
