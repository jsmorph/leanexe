import LeanExe.Source.Scalar

open LeanExe.Source.Scalar

theorem binary_head_unique {head : Lean.Expr} {f g : UInt64 → UInt64 → UInt64}
    (first : Head head f) (second : Head head g) : f = g := by
  cases first with
  | direct operation =>
    cases operation <;> cases second with
    | direct other => cases other; rfl
  | canonical operation result left right instanceType =>
    cases operation <;> cases second with
    | canonical other => cases other; rfl

theorem binary_eval_inv {head a b : Lean.Expr} {values : List Value}
    {f : UInt64 → UInt64 → UInt64} {value : UInt64}
    (meaning : Head head f)
    (evaluation : EvalWith (.app (.app head a) b) values value) :
    ∃ x y, EvalWith a values x ∧ EvalWith b values y ∧ value = f x y := by
  cases meaning with
  | direct operation =>
    cases operation <;> cases evaluation
    all_goals rename_i other left right
    all_goals cases other with
    | direct operation => cases operation; exact ⟨_, _, left, right, rfl⟩
  | canonical operation result leftType rightType instanceType =>
    cases operation <;> cases evaluation
    all_goals rename_i other left right
    all_goals cases other with
    | canonical operation => cases operation; exact ⟨_, _, left, right, rfl⟩
