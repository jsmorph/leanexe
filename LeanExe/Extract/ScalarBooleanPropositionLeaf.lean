import LeanExe.Source.ScalarBooleanPropositionLeaf
import LeanExe.Extract.ScalarSavedBooleanGuard

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Recognize local Boolean propositions without changing the standalone guard path. -/
def booleanPropositionLeaf? : Lean.Expr → Option BooleanPropositionLeaf
  | source@(.app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) _) (.const ``Bool.true [])) =>
      (savedBooleanGuard? source).map BooleanPropositionLeaf.truth
  | .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) left) right =>
      if nontrue : right ≠ .const ``Bool.true [] then
        some (.relation false left right (fun _ => nontrue))
      else none
  | .app (.app (.app (.const ``Ne [.succ .zero]) (.const ``Bool [])) left) right =>
      some (.relation true left right (by intro impossible; cases impossible))
  | _ => none

@[simp] theorem booleanPropositionLeaf_accepts (value : BooleanPropositionLeaf) :
    booleanPropositionLeaf? value.condition = some value := by
  cases value with
  | truth value =>
    have found := savedBooleanGuard_accepts value
    simp only [SavedBooleanGuard.condition] at found
    simp [BooleanPropositionLeaf.condition, SavedBooleanGuard.condition, booleanPropositionLeaf?, found]
  | relation unequal left right nontruth =>
    cases unequal with
    | false => simp [BooleanPropositionLeaf.condition, booleanPropositionLeaf?, nontruth rfl]
    | true => rfl

theorem booleanPropositionLeaf_sound {condition : Lean.Expr} {value : BooleanPropositionLeaf}
    (parsed : booleanPropositionLeaf? condition = some value) : condition = value.condition := by
  unfold booleanPropositionLeaf? at parsed
  split at parsed
  · obtain ⟨truth, found, rfl⟩ := Option.map_eq_some_iff.mp parsed
    exact savedBooleanGuard_sound found
  · split at parsed
    · cases parsed; rfl
    · contradiction
  · cases parsed; rfl
  · contradiction

end LeanExe.Extract.Core
