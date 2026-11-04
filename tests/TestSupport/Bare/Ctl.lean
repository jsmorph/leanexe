import Verified.Reflect.Command

/-!
The step function of the controller loop's test (`docs/native-bare-metal.md`): a first-order
low-pass filter whose state moves a quarter of the way toward the input word in each window.  The
step allocates nothing and cannot trap, so the controller's `main` calls it in every window from
the store that the last window left.
-/

namespace TestSupport.Bare

/-- The new state of the filter from the state `s` and the input `x`. -/
def ctlStep (s x : UInt64) : UInt64 :=
  if s < x then s + (x - s) / 4 else s - (s - x) / 4

verified_compile ctlCompiled := [ctlStep]

end TestSupport.Bare
