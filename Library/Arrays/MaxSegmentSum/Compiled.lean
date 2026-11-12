import Library.Arrays.MaxSegmentSum.Program
import Verified.Reflect.Command

/-! The verified compiler's module of `mss`, `libmss`.  The function borrows its array and
allocates nothing. -/

namespace Library.Arrays.MaxSegmentSum

verified_compile compiled := [mss]

end Library.Arrays.MaxSegmentSum
