import LeanExe.Source.ScalarBooleanSequencePrefix
import LeanExe.Source.ScalarSequence

namespace LeanExe.Source.Scalar.BooleanSequence

/-- Word computations followed by a Boolean-result computation. -/
inductive Eval : Lean.Expr → List Value → Bool → Prop where
  | boolean (body : BooleanRange.Eval source values result) : Eval source values result
  | letWord (input : ResultType) (value : Sequence.Eval a values word)
      (body : Eval b (.word word :: values) result) :
      Eval (.letE name input.expr a b nondep) values result
  | bindWord (input : ResultType) (output : BooleanType) (value : Sequence.Eval a values word)
      (body : Eval b (.word word :: values) result) :
      Eval (BooleanRange.bind name binder input output a b) values result
  | booleanPrefix (shape : BooleanSequencePrefix true)
      (value : BooleanRange.Eval shape.value values flag)
      (body : Eval shape.body (.boolean flag :: values) result) : Eval shape.expr values result
  | run (type : BooleanType) (body : Eval source values result) :
      Eval (BooleanIdentity.run source type) values result
  | pure (type : BooleanType) (body : Eval source values result) :
      Eval (BooleanIdentity.pure source type) values result
  | metadata (body : Eval source values result) : Eval (.mdata data source) values result

/-- The source contract is independent of extraction and generated IR. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | boolean (body : BooleanRange.Supported types source) : Supported types source
  | letWord (input : ResultType) (value : Sequence.Supported types a)
      (body : Supported (.word :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindWord (input : ResultType) (output : BooleanType) (value : Sequence.Supported types a)
      (body : Supported (.word :: types) b) : Supported types (BooleanRange.bind name binder input output a b)
  | booleanPrefix (shape : BooleanSequencePrefix true)
      (value : BooleanRange.Supported types shape.value)
      (body : Supported (.boolean :: types) shape.body) : Supported types shape.expr
  | run (type : BooleanType) (body : Supported types source) : Supported types (BooleanIdentity.run source type)
  | pure (type : BooleanType) (body : Supported types source) : Supported types (BooleanIdentity.pure source type)
  | metadata (body : Supported types source) : Supported types (.mdata data source)

/-- Every admitted sequence terminates for every typed captured environment. -/
theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ result, Eval source values result := by
  induction supported generalizing values with
  | boolean supported =>
    obtain ⟨result, evaluated⟩ := supported.evaluates values typed
    exact ⟨result, .boolean evaluated⟩
  | letWord input value _ second =>
    obtain ⟨word, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := second (.word word :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letWord input evaluated continuation⟩
  | bindWord input output value _ second =>
    obtain ⟨word, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := second (.word word :: values) (by simp [Value.kind, typed])
    exact ⟨result, .bindWord input output evaluated continuation⟩
  | booleanPrefix shape value _ ih =>
    obtain ⟨flag, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .booleanPrefix shape evaluated continuation⟩
  | run type _ ih =>
    obtain ⟨result, evaluated⟩ := ih values typed
    exact ⟨result, .run type evaluated⟩
  | pure type _ ih =>
    obtain ⟨result, evaluated⟩ := ih values typed
    exact ⟨result, .pure type evaluated⟩
  | metadata _ ih =>
    obtain ⟨result, evaluated⟩ := ih values typed
    exact ⟨result, .metadata evaluated⟩

end LeanExe.Source.Scalar.BooleanSequence
