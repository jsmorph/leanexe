import TestSupport.Bare.Theorems
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.ClightN.Read
import ClightNCrc32.Crc32Spec

/-!
The statement `crc32_terminates` of the instance that `clightn/check.sh` writes for the
bare-metal program of `crcCheck 0x3837363534333231 0x39`, CRC-32 of `123456789`: N's program
judgment holds of the definitions and `main` of `clightgen`'s file either with one volatile store
to `lx_out` of each byte of the result and the result 0, or with no event and the code of
`unreachable`, since the entry may abort.  `bare_n` carries the copy's theorem
`crcCompiled.crcCheck.program` to the statement, and the kernel computes the bytes.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

set_option maxHeartbeats 4000000 in
theorem crc32_terminates : stmt_crc32_terminates := by
  refine (bare_n ?_ (TestSupport.Bare.crcCompiled.crcCheck.program _ _) ?_).imp_right And.right
  · inst_ok
  · decide +kernel

end ClightN.Proof

run_cmd ClightN.Read.dump
