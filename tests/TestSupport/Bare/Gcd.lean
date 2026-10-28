import TestSupport.Native.Gcd
import Verified.Bare

/-!
The theorem of the bare-metal program that computes `gcd 1071 462` with the loop of
`loopCompiled`: for every list of CompCert's declarations that `PrefixOk` accepts, the whole
program terminates with result 0 after writing the eight bytes of the result to `lx_out`.
-/

namespace TestSupport.Native.Gcd

bare_program loopCompiled.gcd (1071, 462) [1071, 462] (gcd 1071 462)

end TestSupport.Native.Gcd
