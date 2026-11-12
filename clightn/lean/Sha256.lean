import TestSupport.Bare.Theorems
import LeanExe.Native.ClightN.Instance
import LeanExe.Native.ClightN.Read
import ClightNSha256.Sha256Spec

/-!
The statement `sha256_terminates` of the instance that `clightn/check.sh` writes for the
bare-metal program of `shaCheck 0x636261`, the SHA-256 digest of `abc`: N's program judgment holds
of the definitions and `main` of `clightgen`'s file either with one volatile store to `lx_out` of
each byte of the array of the digest's four words and the result 0, or with no event and the code
of `unreachable`, since the entry may abort.  `bare_n` carries the copy's theorem
`shaCompiled.shaCheck.program` to the statement, and the kernel computes the bytes.
-/

namespace ClightN.Proof

open LClight LeanExe.Native ClightN.Spec

set_option maxHeartbeats 4000000 in
theorem sha256_terminates : stmt_sha256_terminates := by
  refine (bare_n ?_ (TestSupport.Bare.shaCompiled.shaCheck.program _ _)).imp_right And.right
  inst_ok

end ClightN.Proof

run_cmd ClightN.Read.dump
