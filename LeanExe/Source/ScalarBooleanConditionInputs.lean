import LeanExe.Source.ScalarBooleanLocal

namespace LeanExe.Source.Scalar.BooleanConditionForm

def inputs : {value : BooleanLocal} → BooleanConditionForm value → List BooleanLocal
  | _, .truth value => [value]
  | _, .equal left right _ | _, .unequal left right => [left, right]

def denoteInputs {value : BooleanLocal} (form : BooleanConditionForm value)
    (native : BooleanLocal → Bool) : Bool :=
  match form with
  | .truth value => native value
  | .equal left right _ => native left == native right
  | .unequal left right => native left != native right

theorem inputs_size {value : BooleanLocal} (form : BooleanConditionForm value)
    {input : BooleanLocal} (member : input ∈ form.inputs) :
    sizeOf input.expr < sizeOf form.condition := by
  cases form with
  | truth value =>
    simp only [inputs, List.mem_singleton] at member
    subst input
    simp [condition, BooleanLocal.condition]
    omega
  | equal left right nontrue =>
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [condition, booleanRelationCondition] <;> omega
  | unequal left right =>
    simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [condition, booleanRelationCondition] <;> omega

end LeanExe.Source.Scalar.BooleanConditionForm

