import LeanExe.Source.ScalarBooleanFunctionBinding
import LeanExe.Extract.ScalarBooleanRangeSyntax
import LeanExe.Source.ScalarDo
import LeanExe.Source.ExprEquality

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

/-- Peel exact identity wrappers, then remove the helper binder from the argument. -/
def booleanApplicationTail? (source : Lean.Expr) : Option (BooleanApplicationTail × Lean.Expr) :=
  match source with
  | .app (.bvar 0) argument => do
      let value ← LeanExe.Source.ExprProofBinder.drop? 0 argument
      pure (.direct, value)
  | source =>
      match _parsed : booleanRangeWrapper? source with
      | none => none
      | some (wrapper, body) => do
          let (tail, argument) ← booleanApplicationTail? body
          pure (.wrapped wrapper tail, argument)
termination_by sizeOf source
decreasing_by exact booleanRangeWrapper_size _parsed

@[simp] theorem booleanApplicationTail_accepts (tail : BooleanApplicationTail) (argument : Lean.Expr) :
    booleanApplicationTail? (tail.expr argument) = some (tail, argument) := by
  induction tail with
  | direct => simp [BooleanApplicationTail.expr, booleanApplicationTail?]
  | wrapped wrapper tail ih =>
    have parsed := booleanRangeWrapper_accepts wrapper (tail.expr argument)
    cases wrapper <;> simp only [BooleanApplicationTail.expr, BooleanWrapper.expr,
      BooleanIdentity.run, BooleanIdentity.pure] at parsed ⊢
    all_goals rw [booleanApplicationTail?.eq_def]
    all_goals split <;> simp_all
    all_goals split <;> simp_all

theorem booleanApplicationTail_sound {source : Lean.Expr} {tail : BooleanApplicationTail}
    {argument : Lean.Expr} (parsed : booleanApplicationTail? source = some (tail, argument)) :
    source = tail.expr argument := by
  induction source using (measure (fun e : Lean.Expr => sizeOf e)).wf.induction generalizing tail argument with
  | h source ih =>
    rw [booleanApplicationTail?.eq_def] at parsed
    split at parsed
    · rename_i value
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
      obtain ⟨actual, matched, rfl, rfl⟩ := parsed
      rw [LeanExe.Source.ExprProofBinder.drop_sound value 0 matched]
      rfl
    · split at parsed
      · contradiction
      · rename_i wrapper body matched
        simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq, Prod.mk.injEq] at parsed
        obtain ⟨⟨inner, actual⟩, found, rfl, rfl⟩ := parsed
        rw [booleanRangeWrapper_sound matched, ih body (booleanRangeWrapper_size matched) found]
        rfl

/-- Recognize a named Boolean helper application under checked identity wrappers.
The argument cannot refer to the helper binder. -/
def booleanFunctionApplication? : Lean.Expr → Option BooleanFunctionApplication
  | .letE functionName (.forallE typeName input result typeInfo)
      (.lam parameterName domain body valueInfo) continuation nondep =>
      if LeanExe.Source.ExprEquality.same input domain then do
        let result ← booleanType? result
        let (tail, argument) ← booleanApplicationTail? continuation
        pure ⟨⟨functionName, typeName, typeInfo, valueInfo, result, nondep⟩,
          parameterName, input, argument, body, tail⟩
      else none
  | _ => none

@[simp] theorem booleanFunctionApplication_accepts (application : BooleanFunctionApplication) :
    booleanFunctionApplication? application.expr = some application := by
  cases application
  simp [BooleanFunctionApplication.expr, BooleanFunctionBinding.appliedExpr,
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
  · rename_i functionName typeName input result typeInfo parameterName domain body valueInfo continuation nondep
    split at parsed
    · rename_i domains
      have same := LeanExe.Source.ExprEquality.same_eq_true.mp domains
      subst domain
      simp only [bind, pure, Option.bind_eq_some_iff, Option.some.injEq] at parsed
      obtain ⟨resultType, ht, ⟨tail, argument⟩, matched, rfl⟩ := parsed
      rw [booleanType_sound ht, booleanApplicationTail_sound matched]
      rfl
    · contradiction
  · contradiction

theorem booleanFunctionApplication_sizes {expression : Lean.Expr}
    {application : BooleanFunctionApplication}
    (parsed : booleanFunctionApplication? expression = some application) :
    sizeOf application.argument < sizeOf expression ∧ sizeOf application.body < sizeOf expression := by
  rw [booleanFunctionApplication_sound parsed]
  exact ⟨application.argument_size, application.body_size⟩

end LeanExe.Extract.Core
