import Project.Beck.IntegerOrder
import Project.Beck.IntegerMul
import Mathlib.Data.List.MinMax

namespace Project.Beck.BoundarySelect

open LeanExe.Examples.BeckExact IntegerAdd

abbrev Step := Integer × Integer

def ValidStep (step : Step) : Prop := Valid step.1 ∧ Valid step.2 ∧ 0 ≤ value step.2

def select (next old : Step) : Step :=
  if !Integer.isZero next.2 then
    if Integer.isZero old.2 || Integer.less (Integer.mul next.1 old.2) (Integer.mul old.1 next.2)
    then next else old
  else old

def ratio (step : Step) : ℚ := (value step.1 : ℚ) / (value step.2 : ℚ)

def winner (get : ℕ → Step) (jobs : List ℕ) : Option ℕ :=
  (jobs.filter fun job => !Integer.isZero (get job).2).argmin (fun job => ratio (get job))

theorem positive (step : Step) (valid : ValidStep step) (moving : Integer.isZero step.2 = false) :
    0 < value step.2 := by
  have nonzero : value step.2 ≠ 0 := by
    intro zero
    have := (isZero_correct step.2).mpr zero
    rw [moving] at this
    contradiction
  have nonnegative := valid.2.2
  omega

theorem compare (next old : Step) (nextValid : ValidStep next) (oldValid : ValidStep old)
    (nextMoving : Integer.isZero next.2 = false) (oldMoving : Integer.isZero old.2 = false) :
    select next old = if ratio next < ratio old then next else old := by
  have leftProduct := IntegerMul.mul_correct next.1 old.2 nextValid.1 oldValid.2.1
  have rightProduct := IntegerMul.mul_correct old.1 next.2 oldValid.1 nextValid.2.1
  have comparison : Integer.less (Integer.mul next.1 old.2) (Integer.mul old.1 next.2) = true ↔
      ratio next < ratio old := by
    rw [IntegerOrder.less_correct _ _ leftProduct.1 rightProduct.1, leftProduct.2, rightProduct.2,
      ratio, ratio, div_lt_div_iff₀ (by exact_mod_cast positive next nextValid nextMoving)
        (by exact_mod_cast positive old oldValid oldMoving)]
    exact_mod_cast Iff.rfl
  simp only [select, nextMoving, oldMoving, Bool.not_false, ite_true, Bool.false_or, comparison]

theorem winner_member (get : ℕ → Step) (jobs : List ℕ) (job : ℕ)
    (chosen : winner get jobs = some job) : job ∈ jobs ∧ Integer.isZero (get job).2 = false := by
  simpa [winner] using List.argmin_mem chosen

theorem fold_eq_winner (get : ℕ → Step) (jobs : List ℕ)
    (valid : ∀ job ∈ jobs, ValidStep (get job)) :
    jobs.foldl (fun old job => select (get job) old) (Integer.zero, Integer.zero) =
      ((winner get jobs).map get).getD (Integer.zero, Integer.zero) := by
  have zeroFlag : Integer.isZero Integer.zero = true := (isZero_correct _).mpr zero_correct.2
  induction jobs using List.reverseRecOn with
  | nil => simp [winner]
  | append_singleton jobs job ih =>
    have previous := ih (by intro i member; exact valid i (by simp [member]))
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, previous]
    by_cases moving : Integer.isZero (get job).2 = false
    · have filter : (jobs ++ [job]).filter (fun j => !Integer.isZero (get j).2) =
          (jobs.filter fun j => !Integer.isZero (get j).2) ++ [job] := by simp [moving]
      simp only [winner, filter, List.argmin_concat]
      change select (get job) (((winner get jobs).map get).getD (Integer.zero, Integer.zero)) =
        ((Option.casesOn (motive := fun _ => Option ℕ) (winner get jobs) (some job)
          (fun old => if ratio (get job) < ratio (get old) then some job else some old)).map get).getD _
      cases chosen : winner get jobs with
      | none => simp [select, moving, zeroFlag]
      | some old =>
        have member := winner_member get jobs old chosen
        simp only [Option.map_some, Option.getD_some]
        rw [compare (get job) (get old) (valid job (by simp)) (valid old (by simp [member.1])) moving member.2]
        split_ifs <;> rfl
    · have stopped : Integer.isZero (get job).2 = true := by simpa using moving
      have filter : (jobs ++ [job]).filter (fun j => !Integer.isZero (get j).2) =
          jobs.filter (fun j => !Integer.isZero (get j).2) := by simp [stopped]
      simp [select, stopped, winner, filter]

theorem minimum (get : ℕ → Step) (jobs : List ℕ)
    (valid : ∀ job ∈ jobs, ValidStep (get job))
    (moving : ∃ job ∈ jobs, Integer.isZero (get job).2 = false) :
    ∃ first ∈ jobs, Integer.isZero (get first).2 = false ∧
      jobs.foldl (fun old job => select (get job) old) (Integer.zero, Integer.zero) = get first ∧
      ∀ job ∈ jobs, Integer.isZero (get job).2 = false →
        value (get first).1 * value (get job).2 ≤ value (get job).1 * value (get first).2 := by
  cases chosen : winner get jobs with
  | none =>
    have empty := List.argmin_eq_none.mp chosen
    obtain ⟨job, member, flag⟩ := moving
    have included : job ∈ jobs.filter (fun j => !Integer.isZero (get j).2) := by simp [member, flag]
    simp [empty] at included
  | some first =>
    have firstMember := winner_member get jobs first chosen
    refine ⟨first, firstMember.1, firstMember.2, ?_, ?_⟩
    · rw [fold_eq_winner get jobs valid, chosen]
      rfl
    · intro job member flag
      have included : job ∈ jobs.filter (fun j => !Integer.isZero (get j).2) := by simp [member, flag]
      have least := List.le_of_mem_argmin included chosen
      rw [ratio, ratio, div_le_div_iff₀
        (by exact_mod_cast positive (get first) (valid first firstMember.1) firstMember.2)
        (by exact_mod_cast positive (get job) (valid job member) flag)] at least
      exact_mod_cast least

#print axioms minimum

end Project.Beck.BoundarySelect
