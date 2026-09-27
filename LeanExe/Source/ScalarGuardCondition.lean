import LeanExe.Source.ScalarGuard

namespace LeanExe.Source.Scalar

/-- A proposition argument may retain or reduce its leading let bindings. -/
inductive GuardCondition : Guard → Lean.Expr → Prop where
  | retained (guard : Guard) : GuardCondition guard guard.condition
  | letGuard (binding : GuardLet) (body : Guard) (inner : GuardCondition body condition) :
      GuardCondition (.letGuard 0 binding body) (binding.evidence condition)
  | letSaved (binding : GuardLet) (body : BooleanPropositionLeaf) :
      GuardCondition (.letSaved 0 binding body) (binding.evidence body.condition)

/-- Reducing an inner prefix before substitution preserves its binding scope. -/
def Guard.conditionChoices : Guard → List Lean.Expr
  | guard@(.letGuard 0 binding body) => guard.condition :: body.conditionChoices.map binding.evidence
  | guard@(.letSaved 0 binding body) => [guard.condition, binding.evidence body.condition]
  | guard => [guard.condition]

@[simp] theorem Guard.condition_mem_choices (guard : Guard) :
    guard.condition ∈ guard.conditionChoices := by
  cases guard with
  | letGuard n binding body => cases n <;> simp [conditionChoices]
  | letSaved n binding body => cases n <;> simp [conditionChoices]
  | _ => simp [conditionChoices]

theorem GuardCondition.mem_choices {guard : Guard} {condition : Lean.Expr}
    (meaning : GuardCondition guard condition) : condition ∈ guard.conditionChoices := by
  induction meaning with
  | retained guard => exact guard.condition_mem_choices
  | letGuard binding body meaning ih =>
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨_, ih, rfl⟩)
  | letSaved binding body => simp [Guard.conditionChoices]

theorem Guard.conditionChoices_sound (guard : Guard) {condition : Lean.Expr}
    (member : condition ∈ guard.conditionChoices) : GuardCondition guard condition := by
  induction guard generalizing condition with
  | letGuard n binding body ih =>
    cases n with
    | zero =>
      simp only [conditionChoices, List.mem_cons, List.mem_map] at member
      rcases member with rfl | ⟨inner, innerMember, rfl⟩
      · exact .retained _
      · exact .letGuard binding body (ih innerMember)
    | succ n =>
      simp only [conditionChoices, List.mem_singleton] at member
      subst condition
      exact .retained _
  | letSaved n binding body =>
    cases n with
    | zero =>
      simp only [conditionChoices, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .retained _
      · exact .letSaved binding body
    | succ n =>
      simp only [conditionChoices, List.mem_singleton] at member
      subst condition
      exact .retained _
  | _ =>
    simp only [conditionChoices, List.mem_singleton] at member
    subst condition
    exact .retained _

end LeanExe.Source.Scalar
