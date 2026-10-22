import Library.Numerics.Float64.Exp2.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Exp2

verified_compile compiled := [exp2SpecialCase, exp2Core, exp2With, exp10Core, exp10With, exp2,
  exp10]

end Library.Numerics.Float64.Exp2
