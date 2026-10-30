import TestSupport.Bare.Programs
import Verified.Examples.Fold
import Demos.Euler.Verified
import Verified.Bare

/-!
The theorems of the bare-metal programs of test 2 beside GCD: CRC-32 of `123456789`, SHA-256 of
`abc`, the Euler solver on a grid of 16 cells, and a recursion of depth 1,000, which reaches the
depth limit and may end with the code of `unreachable`.
-/

namespace TestSupport.Bare

bare_program crcCompiled.crcCheck (0x3837363534333231, 0x39) [0x3837363534333231, 0x39]
  (crcCheck 0x3837363534333231 0x39)

bare_program shaCompiled.shaCheck 0x636261 [0x636261] (shaCheck 0x636261)

bare_program Demos.Euler.Verified.compiled.solve 4 [4] (Demos.Euler.Buffered.solve 4)

bare_program Verified.Examples.Fold.compiled.recursive 1000 [1000]
  (Verified.Examples.Fold.recursive 1000)

end TestSupport.Bare
