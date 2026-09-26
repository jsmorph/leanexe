import LeanExe.Extract.ScalarBooleanLetTypes
import LeanExe.Source.ScalarPredicateInput

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def predicateInputTypes? (input domain output : Lean.Expr) : Option (ResultType × BooleanType) :=
  if input = domain then
    match input with
    | .app (.const ``Id [.zero]) inner => do
        let input ← scalarResultType? inner
        let output ← booleanType? output
        pure (input, output)
    | _ => none
  else none

@[simp] theorem predicateInputTypes_accepts (input : ResultType) (output : BooleanType) :
    predicateInputTypes? (ResultType.identity input).expr (ResultType.identity input).expr output.expr = some (input, output) := by
  simp [predicateInputTypes?, ResultType.expr]

theorem predicateInputTypes_sound {input domain output : Lean.Expr} {types : ResultType × BooleanType}
    (found : predicateInputTypes? input domain output = some types) :
    input = (ResultType.identity types.1).expr ∧ domain = (ResultType.identity types.1).expr ∧ output = types.2.expr := by
  unfold predicateInputTypes? at found
  split at found
  next same =>
    split at found
    next inner =>
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at found
      obtain ⟨inputType, hi, outputType, ho, rfl⟩ := found
      have hi := scalarResultType_sound hi
      have ho := booleanType_sound ho
      subst inner output
      exact ⟨rfl, same.symm, rfl⟩
    next => contradiction
  next => contradiction

end LeanExe.Extract.Core
