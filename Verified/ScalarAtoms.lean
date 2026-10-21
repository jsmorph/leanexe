import Verified.ScalarTransport

namespace Wasm

theorem OneUniform.localSet (m : Module) (index : Nat) : OneUniform m (.localSet index) := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore]
  | succ fuel =>
    simp only [execOne.eq_def]
    split <;> first | rfl | (split <;> rfl)

theorem OneNoReturnCall.localSet (m : Module) (index : Nat) :
    OneNoReturnCall m (.localSet index) := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.noReturnCall]
  | succ fuel =>
    simp only [execOne.eq_def]
    split <;> first | rfl | (split <;> rfl)

theorem OneUniform.localGet (m : Module) (index : Nat) : OneUniform m (.localGet index) := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneNoReturnCall.localGet (m : Module) (index : Nat) : OneNoReturnCall m (.localGet index) := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneUniform.constI64 (m : Module) (value : UInt64) : OneUniform m (.constI64 value) := by
  intro fuel host store reference locals
  cases fuel <;> simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]

theorem OneNoReturnCall.constI64 (m : Module) (value : UInt64) : OneNoReturnCall m (.constI64 value) := by
  intro fuel host store locals
  cases fuel <;> simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]

theorem OneUniform.addI64 (m : Module) : OneUniform m .addI64 := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneNoReturnCall.addI64 (m : Module) : OneNoReturnCall m .addI64 := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneUniform.mulI64 (m : Module) : OneUniform m .mulI64 := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneNoReturnCall.mulI64 (m : Module) : OneNoReturnCall m .mulI64 := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneUniform.f64Const (m : Module) (value : UInt64) : OneUniform m (.f64Const value) := by
  intro fuel host store reference locals
  cases fuel <;> simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]

theorem OneNoReturnCall.f64Const (m : Module) (value : UInt64) : OneNoReturnCall m (.f64Const value) := by
  intro fuel host store locals
  cases fuel <;> simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]

theorem OneUniform.f64Add (m : Module) : OneUniform m .f64Add := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneNoReturnCall.f64Add (m : Module) : OneNoReturnCall m .f64Add := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneUniform.f64Mul (m : Module) : OneUniform m .f64Mul := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl

theorem OneNoReturnCall.f64Mul (m : Module) : OneNoReturnCall m .f64Mul := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore, Continuation.noReturnCall]
  | succ fuel => simp only [execOne.eq_def]; split <;> rfl


end Wasm
