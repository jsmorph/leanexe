import Library.Numerics.Statistics.Mean.Program
import Verified.Reflect.Command

/-! The verified compiler's module of `mean`.  The function allocates nothing, so the generated
`compiled.mean.implements` states that function 2 computes `mean` without a trap. -/

namespace Library.Numerics.Statistics.Mean

verified_compile compiled := [mean]

end Library.Numerics.Statistics.Mean
