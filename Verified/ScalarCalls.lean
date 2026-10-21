import Verified.ScalarTransport

namespace Wasm

theorem OneUniform.call {m : Module} {entry : Nat} (callee : EntryUniform m entry) :
    OneUniform m (.call entry) := by
  intro fuel host store reference locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.withStore]
  | succ fuel =>
    simp only [execOne.eq_def]
    rw [callee fuel host store reference locals.values]
    cases h : run fuel m entry reference locals.values host <;> rfl

theorem OneNoReturnCall.call (m : Module) (entry : Nat) : OneNoReturnCall m (.call entry) := by
  intro fuel host store locals
  cases fuel with
  | zero => simp only [execOne.eq_def, Continuation.noReturnCall]
  | succ fuel =>
    simp only [execOne.eq_def]
    cases h : run fuel m entry store locals.values host <;> rfl

#print axioms OneUniform.call

end Wasm
