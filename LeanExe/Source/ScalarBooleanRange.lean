import LeanExe.Source.ScalarRangeExitSupported

namespace LeanExe.Source.Scalar.BooleanRange

/-- A word-valued loop followed by a Boolean result computation. -/
inductive Eval : Lean.Expr → List Value → Bool → Prop where
  | letResult (value : Range.Exit.Eval a values x)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) b) (.word x :: values) flag.toUInt64) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values flag
  | wrapped (wrapper : BooleanWrapper) (body : Eval source values flag) :
      Eval (wrapper.expr source) values flag

/-- Source support checks both the loop and its Boolean continuation. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | letResult (value : Range.Exit.Supported types a)
      (body : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) b)) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | wrapped (wrapper : BooleanWrapper) (body : Supported types source) :
      Supported types (wrapper.expr source)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ flag, Eval source values flag := by
  induction supported generalizing values with
  | letResult value body =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨result, hr⟩ := body.evaluates (.word x :: values) (by simp [Value.kind, typed])
    obtain ⟨flag, rfl⟩ := hr.booleanConversion_result
    exact ⟨flag, .letResult hx hr⟩
  | wrapped wrapper _ ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    exact ⟨flag, .wrapped wrapper evaluated⟩

end LeanExe.Source.Scalar.BooleanRange
