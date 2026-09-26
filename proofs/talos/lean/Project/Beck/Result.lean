import Project.Beck.Discrepancy
import Project.Beck.Parser

namespace Project.Beck.Result

open LeanExe.Examples.Beck

def group (x : Point) (job : Nat) : UInt64 := if negative x.numerators[job]! then 0 else 1

def output (input : Input) (x : Point) : Array UInt64 :=
  #[0, input.overlap.toUInt64] ++ ((List.range input.jobs).map (group x)).toArray

abbrev finalPoint (input : Input) : Point := rounds input.jobs input ⟨1, Array.replicate input.jobs 0⟩

theorem compute_eq (words : Array UInt64) (accepted : (readInput words).status = 0)
    (supported : State.Supported (readInput words)) :
    compute words = output (readInput words) (finalPoint (readInput words)) := by
  have nonzero := (Loop.initial_finishes (readInput words) supported).1
  simp only [compute, accepted, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  change (if (finalPoint (readInput words)).denominator == 0 then _ else _) = _
  rw [show ((finalPoint (readInput words)).denominator == 0) = false by simpa using nonzero]
  simp only [Bool.false_eq_true, ↓reduceIte, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range', bind, pure]
  have loop := List.forIn_pure_yield_eq_foldl (m := Id) (l := List.range (readInput words).jobs)
    (fun job (acc : Array UInt64) => acc.push (group (finalPoint (readInput words)) job))
    #[0, (readInput words).overlap.toUInt64]
  exact loop.trans (by simp [pure, output])

theorem output_size (input : Input) (x : Point) : (output input x).size = input.jobs + 2 := by
  simp [output]

theorem output_status (input : Input) (x : Point) : (output input x)[0]! = 0 := by simp [output]

theorem output_overlap (input : Input) (x : Point) : (output input x)[1]! = input.overlap.toUInt64 := by
  simp [output]

theorem output_group (input : Input) (x : Point) (job : Nat) (hj : job < input.jobs) :
    (output input x)[job + 2]! = group x job := by
  have bound : job + 2 < (output input x).size := by rw [output_size]; omega
  rw [getElem!_pos (output input x) (job + 2) bound]
  simp only [output]
  rw [Array.getElem_append_right (by change 2 ≤ job + 2; omega)]
  simp

theorem group_assigned (x : Point) (job : Nat) : group x job = 0 ∨ group x job = 1 := by
  unfold group
  split <;> simp

theorem sign_count (input : Input) (x : Point) (category : Fin input.categories) :
    (∑ job ∈ Counting.members input category, Discrepancy.sign x job.val) =
      (((Counting.members input category).filter fun job => group x job.val = 1).card : ℤ) -
        ((Counting.members input category).filter fun job => group x job.val = 0).card := by
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro job _
  unfold Discrepancy.sign group
  split <;> norm_num [show (0 : UInt64) ≠ 1 by decide, show (1 : UInt64) ≠ 0 by decide]

theorem output_discrepancy (input : Input) (supported : State.Supported input)
    (category : Fin input.categories) :
    |(((Counting.members input category).filter fun job =>
        (output input (finalPoint input))[job.val + 2]! = 1).card : ℤ) -
      ((Counting.members input category).filter fun job =>
        (output input (finalPoint input))[job.val + 2]! = 0).card| ≤
      max 0 (2 * (input.overlap : ℤ) - 1) := by
  simp_rw [output_group input (finalPoint input) _ (Fin.isLt _)]
  rw [← sign_count]
  exact Discrepancy.initial_discrepancy input supported category

theorem compute_discrepancy (words : Array UInt64) (accepted : (readInput words).status = 0)
    (category : Fin (readInput words).categories) :
    (compute words).size = (readInput words).jobs + 2 ∧ (compute words)[0]! = 0 ∧
      (compute words)[1]! = (readInput words).overlap.toUInt64 ∧
      (∀ job < (readInput words).jobs, (compute words)[job + 2]! = 0 ∨ (compute words)[job + 2]! = 1) ∧
      |(((Counting.members (readInput words) category).filter fun job =>
          (compute words)[job.val + 2]! = 1).card : ℤ) -
        ((Counting.members (readInput words) category).filter fun job =>
          (compute words)[job.val + 2]! = 0).card| ≤
        max 0 (2 * ((readInput words).overlap : ℤ) - 1) := by
  have supported := Parser.accepted_supported words accepted
  rw [compute_eq words accepted supported]
  refine ⟨output_size _ _, output_status _ _, output_overlap _ _, ?_, output_discrepancy _ supported category⟩
  intro job hj
  rw [output_group _ _ job hj]
  exact group_assigned _ _

theorem compute_rejected (words : Array UInt64) (rejected : (readInput words).status ≠ 0) :
    compute words = #[(readInput words).status] := by
  simp [compute, rejected]

theorem compute_success (words : Array UInt64) (accepted : (readInput words).status = 0) :
    (compute words).size = (readInput words).jobs + 2 ∧ (compute words)[0]! = 0 ∧
      (compute words)[1]! = (readInput words).overlap.toUInt64 ∧
      ∀ job < (readInput words).jobs, (compute words)[job + 2]! = 0 ∨ (compute words)[job + 2]! = 1 := by
  rw [compute_eq words accepted (Parser.accepted_supported words accepted)]
  refine ⟨output_size _ _, output_status _ _, output_overlap _ _, ?_⟩
  intro job hj
  rw [output_group _ _ job hj]
  exact group_assigned _ _

end Project.Beck.Result
