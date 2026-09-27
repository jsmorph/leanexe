import LeanExe.Source.ScalarBooleanSequencePrefix
import LeanExe.Source.ScalarWordRange

namespace LeanExe.Source.Scalar.Sequence

/-- Sequential word computations, with earlier results available to later loops. -/
inductive Eval : Lean.Expr → List Value → UInt64 → Prop where
  | word (body : WordRange.Eval source values result) : Eval source values result
  | letWord (input : ResultType) (value : Eval a values word)
      (body : Eval b (.word word :: values) result) :
      Eval (.letE name input.expr a b nondep) values result
  | bindWord (input output : ResultType) (value : Eval a values word)
      (body : Eval b (.word word :: values) result) :
      Eval (Identity.bind name binder a b input output) values result
  | booleanPrefix (shape : BooleanSequencePrefix false)
      (value : BooleanRange.Eval shape.value values flag)
      (body : Eval shape.body (.boolean flag :: values) result) : Eval shape.expr values result
  | run (type : ResultType) (body : Eval source values result) :
      Eval (Identity.run source type) values result
  | pure (type : ResultType) (body : Eval source values result) :
      Eval (Identity.pure source type) values result
  | metadata (body : Eval source values result) : Eval (.mdata data source) values result

/-- The source contract is independent of extraction and generated IR. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | word (body : WordRange.Supported types source) : Supported types source
  | letWord (input : ResultType) (value : Supported types a)
      (body : Supported (.word :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindWord (input output : ResultType) (value : Supported types a)
      (body : Supported (.word :: types) b) : Supported types (Identity.bind name binder a b input output)
  | booleanPrefix (shape : BooleanSequencePrefix false)
      (value : BooleanRange.Supported types shape.value)
      (body : Supported (.boolean :: types) shape.body) : Supported types shape.expr
  | run (type : ResultType) (body : Supported types source) : Supported types (Identity.run source type)
  | pure (type : ResultType) (body : Supported types source) : Supported types (Identity.pure source type)
  | metadata (body : Supported types source) : Supported types (.mdata data source)

/-- Every admitted sequence terminates for every typed captured environment. -/
theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ result, Eval source values result := by
  induction supported generalizing values with
  | word supported =>
    obtain ⟨result, evaluated⟩ := supported.evaluates values typed
    exact ⟨result, .word evaluated⟩
  | letWord input _ _ first second =>
    obtain ⟨word, evaluated⟩ := first values typed
    obtain ⟨result, continuation⟩ := second (.word word :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letWord input evaluated continuation⟩
  | bindWord input output _ _ first second =>
    obtain ⟨word, evaluated⟩ := first values typed
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

end LeanExe.Source.Scalar.Sequence
