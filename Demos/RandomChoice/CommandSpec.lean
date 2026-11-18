import Demos.RandomChoice.Spec
import Demos.RandomHistogram.CommandSpec

namespace Demos.RandomChoice

open LeanExe LeanExe.Wasi

/-- The picks of the accepted words of `ws` for the range [1, n], in order. -/
def accepted (n : UInt64) (ws : List UInt64) : List UInt64 :=
  (ws.map fun w => pickSpec (n, w)).filter (· != 0)

/-- The cap of the loop's passes for K values, each pass of 512 words: `K / 128 + 3`. -/
def passes (k : UInt64) : UInt64 := k / 128 + 3

/-- The status of a run whose passes reach the cap with values still to choose: 77, the least
status above the WASI errnos, 0 to 76. -/
def capStatus : UInt64 := 77

end Demos.RandomChoice
