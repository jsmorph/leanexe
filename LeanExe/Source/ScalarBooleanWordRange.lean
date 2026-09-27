import LeanExe.Source.ScalarBooleanRange

namespace LeanExe.Source.Scalar.BooleanWordRange

/-- Standard Id sequencing from a Boolean action to a word continuation. -/
def bind (name : Lean.Name) (binder : Lean.BinderInfo) (input : BooleanType)
    (output : ResultType) (value body : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.app (.const ``Bind.bind [.zero, .zero]) (.const ``Id [.zero]))
    (.app (.app (.const ``Monad.toBind [.zero, .zero]) (.const ``Id [.zero]))
      (.const ``Id.instMonad [.zero]))) input.expr) output.expr) value)
    (.lam name input.expr body binder)

/-- A Boolean loop can feed an arbitrary admitted pure word continuation. -/
inductive Eval : Lean.Expr → List Value → UInt64 → Prop where
  | letResult (input : BooleanType) (value : BooleanRange.Eval a values flag)
      (body : EvalWith b (.boolean flag :: values) result) :
      Eval (.letE name input.expr a b nondep) values result
  | bindResult (input : BooleanType) (output : ResultType)
      (value : BooleanRange.Eval a values flag) (body : EvalWith b (.boolean flag :: values) result) :
      Eval (bind name binder input output a b) values result
  | converted (value : BooleanRange.Eval source values flag) :
      Eval (.app (.const ``Bool.toUInt64 []) source) values flag.toUInt64
  | run (type : ResultType) (body : Eval source values result) : Eval (Identity.run source type) values result
  | pure (type : ResultType) (body : Eval source values result) : Eval (Identity.pure source type) values result
  | metadata (body : Eval source values result) : Eval (.mdata data source) values result

inductive Supported : List BindingKind → Lean.Expr → Prop where
  | letResult (input : BooleanType) (value : BooleanRange.Supported types a)
      (body : SupportedWith (.boolean :: types) b) : Supported types (.letE name input.expr a b nondep)
  | bindResult (input : BooleanType) (output : ResultType)
      (value : BooleanRange.Supported types a) (body : SupportedWith (.boolean :: types) b) :
      Supported types (bind name binder input output a b)
  | converted (value : BooleanRange.Supported types source) :
      Supported types (.app (.const ``Bool.toUInt64 []) source)
  | run (type : ResultType) (body : Supported types source) : Supported types (Identity.run source type)
  | pure (type : ResultType) (body : Supported types source) : Supported types (Identity.pure source type)
  | metadata (body : Supported types source) : Supported types (.mdata data source)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value) (typed : values.map Value.kind = types) :
    ∃ result, Eval source values result := by
  induction supported with
  | letResult input value body =>
    obtain ⟨flag, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := body.evaluates (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letResult input evaluated continuation⟩
  | bindResult input output value body =>
    obtain ⟨flag, evaluated⟩ := value.evaluates values typed
    obtain ⟨result, continuation⟩ := body.evaluates (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .bindResult input output evaluated continuation⟩
  | converted value =>
    obtain ⟨flag, evaluated⟩ := value.evaluates values typed
    exact ⟨flag.toUInt64, .converted evaluated⟩
  | run type _ ih => obtain ⟨result, evaluated⟩ := ih; exact ⟨result, .run type evaluated⟩
  | pure type _ ih => obtain ⟨result, evaluated⟩ := ih; exact ⟨result, .pure type evaluated⟩
  | metadata _ ih => obtain ⟨result, evaluated⟩ := ih; exact ⟨result, .metadata evaluated⟩

end LeanExe.Source.Scalar.BooleanWordRange
