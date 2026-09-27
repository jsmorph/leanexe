import LeanExe.Source.ScalarRangeExitSupported
import LeanExe.Source.ScalarBooleanLet

namespace LeanExe.Source.Scalar.BooleanRange

/-- Standard Id sequencing retains its input and Boolean result annotations. -/
def bind (name : Lean.Name) (binder : Lean.BinderInfo) (input : ResultType)
    (output : BooleanType) (value body : Lean.Expr) : Lean.Expr :=
  (BooleanBindingForm.monadic binder output).expr name input.expr value body

def bindBoolean (name : Lean.Name) (binder : Lean.BinderInfo) (input output : BooleanType)
    (value body : Lean.Expr) : Lean.Expr :=
  (BooleanBindingForm.monadic binder output).expr name input.expr value body

/-- A word-valued loop followed by a Boolean result computation. -/
inductive Eval : Lean.Expr → List Value → Bool → Prop where
  | letFlagBefore (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values flag.toUInt64)
      (body : Eval b (.boolean flag :: values) result) :
      Eval (.letE name (.const ``Bool []) a b nondep) values result
  | bindFlagBefore (input output : BooleanType)
      (value : EvalWith (.app (.const ``Bool.toUInt64 []) a) values flag.toUInt64)
      (body : Eval b (.boolean flag :: values) result) :
      Eval (bindBoolean name binder input output a b) values result
  | letBefore (value : EvalWith a values x) (body : Eval b (.word x :: values) flag) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values flag
  | bindBefore (input : ResultType) (output : BooleanType)
      (value : EvalWith a values x) (body : Eval b (.word x :: values) flag) :
      Eval (bind name binder input output a b) values flag
  | letResult (value : Range.Exit.Eval a values x)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) b) (.word x :: values) flag.toUInt64) :
      Eval (.letE name (.const ``UInt64 []) a b nondep) values flag
  | bindResult (input : ResultType) (output : BooleanType)
      (value : Range.Exit.Eval a values x)
      (body : EvalWith (.app (.const ``Bool.toUInt64 []) b) (.word x :: values) flag.toUInt64) :
      Eval (bind name binder input output a b) values flag
  | idLet (type : Lean.Expr)
      (body : Eval (.letE name type value tail nondep) values result) :
      Eval (.letE name (.app (.const ``Id [.zero]) type) value tail nondep) values result
  | wrapped (wrapper : BooleanWrapper) (body : Eval source values flag) :
      Eval (wrapper.expr source) values flag

/-- Source support checks both the loop and its Boolean continuation. -/
inductive Supported : List BindingKind → Lean.Expr → Prop where
  | letFlagBefore (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) :
      Supported types (.letE name (.const ``Bool []) a b nondep)
  | bindFlagBefore (input output : BooleanType)
      (value : SupportedWith types (.app (.const ``Bool.toUInt64 []) a))
      (body : Supported (.boolean :: types) b) :
      Supported types (bindBoolean name binder input output a b)
  | letBefore (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | bindBefore (input : ResultType) (output : BooleanType)
      (value : SupportedWith types a) (body : Supported (.word :: types) b) :
      Supported types (bind name binder input output a b)
  | letResult (value : Range.Exit.Supported types a)
      (body : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) b)) :
      Supported types (.letE name (.const ``UInt64 []) a b nondep)
  | bindResult (input : ResultType) (output : BooleanType)
      (value : Range.Exit.Supported types a)
      (body : SupportedWith (.word :: types) (.app (.const ``Bool.toUInt64 []) b)) :
      Supported types (bind name binder input output a b)
  | idLet (type : Lean.Expr)
      (body : Supported types (.letE name type value tail nondep)) :
      Supported types (.letE name (.app (.const ``Id [.zero]) type) value tail nondep)
  | wrapped (wrapper : BooleanWrapper) (body : Supported types source) :
      Supported types (wrapper.expr source)

theorem Supported.evaluates {types : List BindingKind} {source : Lean.Expr}
    (supported : Supported types source) (values : List Value)
    (typed : values.map Value.kind = types) : ∃ flag, Eval source values flag := by
  induction supported generalizing values with
  | letFlagBefore value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨result, body⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .letFlagBefore evaluated body⟩
  | bindFlagBefore input output value _ ih =>
    obtain ⟨encoded, evaluated⟩ := value.evaluates values typed
    obtain ⟨flag, rfl⟩ := evaluated.booleanConversion_result
    obtain ⟨result, body⟩ := ih (.boolean flag :: values) (by simp [Value.kind, typed])
    exact ⟨result, .bindFlagBefore input output evaluated body⟩
  | letBefore value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨flag, evaluated⟩ := ih (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨flag, .letBefore hx evaluated⟩
  | bindBefore input output value _ ih =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨flag, evaluated⟩ := ih (.word x :: values) (by simp [Value.kind, typed])
    exact ⟨flag, .bindBefore input output hx evaluated⟩
  | letResult value body =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨result, hr⟩ := body.evaluates (.word x :: values) (by simp [Value.kind, typed])
    obtain ⟨flag, rfl⟩ := hr.booleanConversion_result
    exact ⟨flag, .letResult hx hr⟩
  | bindResult input output value body =>
    obtain ⟨x, hx⟩ := value.evaluates values typed
    obtain ⟨result, hr⟩ := body.evaluates (.word x :: values) (by simp [Value.kind, typed])
    obtain ⟨flag, rfl⟩ := hr.booleanConversion_result
    exact ⟨flag, .bindResult input output hx hr⟩
  | idLet type _ ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    exact ⟨flag, .idLet type evaluated⟩
  | wrapped wrapper _ ih =>
    obtain ⟨flag, evaluated⟩ := ih values typed
    exact ⟨flag, .wrapped wrapper evaluated⟩

end LeanExe.Source.Scalar.BooleanRange
