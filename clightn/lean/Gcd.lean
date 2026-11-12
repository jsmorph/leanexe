import TestSupport.Bare.Gcd
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.ClightN.Read
import ClightNGcd.GcdSpec

/-!
The statement `gcd_terminates` of the instance that `clightn/check.sh` writes for the bare-metal
program of `gcd 1071 462`: N's program judgment holds of the definitions and `main` of
`clightgen`'s file with one volatile store to `lx_out` of each byte of the result and the result
0.  `bare_n` carries the copy's theorem `loopCompiled.gcd.program`, whose entry cannot abort, to
the statement, and the kernel computes the bytes from `gcd_value`.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

theorem gcd_value : TestSupport.Native.Gcd.gcd 1071 462 = 21 := by
  rw [TestSupport.Native.Gcd.gcd, TestSupport.Native.Gcd.gcd, TestSupport.Native.Gcd.gcd,
    TestSupport.Native.Gcd.gcd, TestSupport.Native.Gcd.gcd]
  decide

set_option maxHeartbeats 4000000 in
theorem gcd_terminates : stmt_gcd_terminates := by
  refine (bare_n ?_ (TestSupport.Native.Gcd.loopCompiled.gcd.program _ _)).resolve_right
    fun h => Bool.false_ne_true h.1
  rw [gcd_value]
  inst_ok

end ClightN.Proof

run_cmd ClightN.Read.dump
