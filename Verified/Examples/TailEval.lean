module

public import Verified.Examples.Tail

@[expose] public section

/-! This module imports the compilation of `sharedSeed` and its tail loop `tailGrow`, and it sees
the theorem `compiled.tailGrow.wellFounded` without its proof.  The kernel still evaluates the bound
of `sharedSeed`, since `Verified.Tail.rank` counts the loop's steps from its step function alone. -/

namespace Verified.Examples.TailEval

open Verified.Examples.Tail

theorem sharedSeed_bound :
    compiled.sharedSeed.bound (10, #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]) = 1136 := by
  decide +kernel

#print axioms sharedSeed_bound

end Verified.Examples.TailEval
