import Verified.ScalarTransport

namespace Wasm

theorem OneUniform.block {m : Module} {body : Program} (uniform : CodeUniform m body)
    (params results : Nat) (paramTypes resultTypes : List ValueType) :
    OneUniform m (.block params results body paramTypes resultTypes) := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore]
  | succ fuel =>
    simp only [execOne.eq_def]
    rw [uniform fuel host store reference locals]
    cases h : exec fuel m reference locals body host with
    | Fallthrough state after => rfl
    | Break label state after => cases label <;> rfl
    | Return state values => rfl
    | Trap state message => rfl
    | Invalid message => rfl
    | OutOfFuel => rfl
    | ReturnCall entry state values => rfl
    | Throwing tag values state after => rfl

theorem OneNoReturnCall.block {m : Module} {body : Program}
    (safe : CodeNoReturnCall m body)
    (params results : Nat) (paramTypes resultTypes : List ValueType) :
    OneNoReturnCall m (.block params results body paramTypes resultTypes) := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.noReturnCall]
  | succ fuel =>
    have hSafe := safe fuel host store locals
    simp only [execOne.eq_def]
    cases h : exec fuel m store locals body host with
    | Fallthrough state after => rfl
    | Break label state after => cases label <;> rfl
    | Return state values => rfl
    | Trap state message => rfl
    | Invalid message => rfl
    | OutOfFuel => rfl
    | ReturnCall entry state values => simp only [h, Continuation.noReturnCall, Bool.false_eq_true] at hSafe
    | Throwing tag values state after => rfl

theorem OneUniform.loop {m : Module} {body : Program} (uniform : CodeUniform m body)
    (params results : Nat) (paramTypes resultTypes : List ValueType) :
    OneUniform m (.loop params results body paramTypes resultTypes) := by
  intro fuel
  induction fuel with
  | zero =>
    intro host store reference locals
    simp only [execOne.eq_def, Continuation.withStore]
  | succ fuel ih =>
    intro host store reference locals
    rw [execOne_loop_succ fuel m store locals host params results body paramTypes resultTypes,
      execOne_loop_succ fuel m reference locals host params results body paramTypes resultTypes]
    rw [uniform fuel host store reference locals]
    cases h : exec fuel m reference locals body host with
    | Fallthrough state after => rfl
    | Break label state after =>
      cases label with
      | zero => exact ih host store state _
      | succ label => rfl
    | Return state values => rfl
    | Trap state message => rfl
    | Invalid message => rfl
    | OutOfFuel => rfl
    | ReturnCall entry state values => rfl
    | Throwing tag values state after => rfl

theorem OneNoReturnCall.loop {m : Module} {body : Program}
    (safe : CodeNoReturnCall m body)
    (params results : Nat) (paramTypes resultTypes : List ValueType) :
    OneNoReturnCall m (.loop params results body paramTypes resultTypes) := by
  intro fuel
  induction fuel with
  | zero =>
    intro host store locals
    simp only [execOne.eq_def, Continuation.noReturnCall]
  | succ fuel ih =>
    intro host store locals
    have hSafe := safe fuel host store locals
    rw [execOne_loop_succ fuel m store locals host params results body paramTypes resultTypes]
    cases h : exec fuel m store locals body host with
    | Fallthrough state after => rfl
    | Break label state after =>
      cases label with
      | zero => exact ih host state _
      | succ label => rfl
    | Return state values => rfl
    | Trap state message => rfl
    | Invalid message => rfl
    | OutOfFuel => rfl
    | ReturnCall entry state values => simp only [h, Continuation.noReturnCall, Bool.false_eq_true] at hSafe
    | Throwing tag values state after => rfl

theorem CodeUniform.ite {m : Module} {first second : Program} {condition : Prop}
    [Decidable condition] (hFirst : CodeUniform m first) (hSecond : CodeUniform m second) :
    CodeUniform m (if condition then first else second) := by
  split <;> assumption

theorem CodeNoReturnCall.ite {m : Module} {first second : Program} {condition : Prop}
    [Decidable condition] (hFirst : CodeNoReturnCall m first)
    (hSecond : CodeNoReturnCall m second) :
    CodeNoReturnCall m (if condition then first else second) := by
  split <;> assumption

theorem OneUniform.iff {m : Module} {first second : Program}
    (hFirst : CodeUniform m first) (hSecond : CodeUniform m second)
    (params results : Nat) (paramTypes resultTypes : List ValueType) :
    OneUniform m (.iff params results first second paramTypes resultTypes) := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore]
  | succ fuel =>
    simp only [execOne.eq_def]
    split
    next _ condition values _ =>
      rw [(CodeUniform.ite hFirst hSecond) fuel host store reference]
      cases h : exec fuel m reference { locals with values := values }
          (if condition ≠ 0 then first else second) host with
      | Fallthrough state after => rfl
      | Break label state after => cases label <;> rfl
      | Return state values => rfl
      | Trap state message => rfl
      | Invalid message => rfl
      | OutOfFuel => rfl
      | ReturnCall entry state values => rfl
      | Throwing tag values state after => rfl
    next => rfl

theorem OneNoReturnCall.iff {m : Module} {first second : Program}
    (hFirst : CodeNoReturnCall m first) (hSecond : CodeNoReturnCall m second)
    (params results : Nat) (paramTypes resultTypes : List ValueType) :
    OneNoReturnCall m (.iff params results first second paramTypes resultTypes) := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.noReturnCall]
  | succ fuel =>
    simp only [execOne.eq_def]
    split
    next _ condition values _ =>
      have hSafe := (CodeNoReturnCall.ite (condition := condition ≠ 0) hFirst hSecond) fuel host store
        { locals with values := values }
      cases h : exec fuel m store { locals with values := values }
          (if condition ≠ 0 then first else second) host with
      | Fallthrough state after => rfl
      | Break label state after => cases label <;> rfl
      | Return state values => rfl
      | Trap state message => rfl
      | Invalid message => rfl
      | OutOfFuel => rfl
      | ReturnCall entry state values =>
        simp only [h, Continuation.noReturnCall, Bool.false_eq_true] at hSafe
      | Throwing tag values state after => rfl
    next => rfl

end Wasm
