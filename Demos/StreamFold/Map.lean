import Demos.StreamFold.Interface

namespace Demos.StreamFold

theorem repeatWhile_go_map (view : α → β) (leftTest : α → Bool) (rightTest : β → Bool)
    (leftStep : α → α) (rightStep : β → β)
    (test : ∀ state, rightTest (view state) = leftTest state)
    (step : ∀ state, view (leftStep state) = rightStep (view state)) (fuel : Nat) (state : α) :
    view (LeanExe.repeatWhile.go leftTest leftStep fuel state) =
      LeanExe.repeatWhile.go rightTest rightStep fuel (view state) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [LeanExe.repeatWhile.go, test]
      split
      · rw [ih, step]
      · rfl

theorem repeatWhile_map (view : α → β) (leftTest : α → Bool) (rightTest : β → Bool)
    (leftStep : α → α) (rightStep : β → β)
    (test : ∀ state, rightTest (view state) = leftTest state)
    (step : ∀ state, view (leftStep state) = rightStep (view state)) (fuel : UInt64) (state : α) :
    view (LeanExe.repeatWhile fuel state leftTest leftStep) =
      LeanExe.repeatWhile fuel (view state) rightTest rightStep :=
  repeatWhile_go_map view leftTest rightTest leftStep rightStep test step fuel.toNat state

end Demos.StreamFold
