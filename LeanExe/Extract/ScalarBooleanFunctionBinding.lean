import LeanExe.Source.ScalarBooleanFunctionBinding
import LeanExe.Extract.ScalarBooleanType
import LeanExe.Source.ScalarDo
import LeanExe.Source.ExprEquality

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Recognize a direct named helper application. Its argument cannot use the
helper binder; removing that binder preserves every outer reference. -/
def booleanFunctionApplication? : Lean.Expr → Option BooleanFunctionApplication
  | .letE functionName (.forallE typeName input result typeInfo)
      (.lam parameterName domain body valueInfo) (.app (.bvar 0) argument) nondep =>
      if LeanExe.Source.ExprEquality.same input domain then do
        let result ← booleanType? result
        let argument ← LeanExe.Source.ExprProofBinder.drop? 0 argument
        pure ⟨⟨functionName, typeName, typeInfo, valueInfo, result, nondep⟩,
          parameterName, input, argument, body⟩
      else none
  | _ => none

@[simp] theorem booleanFunctionApplication_accepts (application : BooleanFunctionApplication) :
    booleanFunctionApplication? application.expr = some application := by
  cases application
  simp [BooleanFunctionApplication.expr, BooleanFunctionBinding.expr,
    booleanFunctionApplication?]

@[simp] theorem booleanFunctionApplication_wordLet (name : Lean.Name) (type : ResultType)
    (value body : Lean.Expr) (nondep : Bool) :
    booleanFunctionApplication? (.letE name type.expr value body nondep) = none := by
  cases type <;> rfl

@[simp] theorem booleanFunctionApplication_booleanLet (name : Lean.Name) (type : BooleanType)
    (value body : Lean.Expr) (nondep : Bool) :
    booleanFunctionApplication? (.letE name type.expr value body nondep) = none := by
  cases type <;> rfl

theorem booleanFunctionApplication_sound {expression : Lean.Expr}
    {application : BooleanFunctionApplication}
    (parsed : booleanFunctionApplication? expression = some application) :
    expression = application.expr := by
  unfold booleanFunctionApplication? at parsed
  split at parsed
  · rename_i functionName typeName input result typeInfo parameterName domain body valueInfo argument nondep
    split at parsed
    · rename_i domains
      have same := LeanExe.Source.ExprEquality.same_eq_true.mp domains
      subst domain
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨resultType, ht, value, hv, rfl⟩ := parsed
      have typeShape := booleanType_sound ht
      have valueShape := LeanExe.Source.ExprProofBinder.drop_sound argument 0 hv
      simp [BooleanFunctionApplication.expr, BooleanFunctionBinding.expr, typeShape, valueShape]
    · contradiction
  · contradiction

theorem booleanFunctionApplication_sizes {expression : Lean.Expr}
    {application : BooleanFunctionApplication}
    (parsed : booleanFunctionApplication? expression = some application) :
    sizeOf application.argument < sizeOf expression ∧ sizeOf application.body < sizeOf expression := by
  rw [booleanFunctionApplication_sound parsed]
  exact ⟨application.argument_size, application.body_size⟩

end LeanExe.Extract.Core
