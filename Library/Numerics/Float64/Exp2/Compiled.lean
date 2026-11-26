module

public import Library.Numerics.Float64.Exp2.Program
public import Verified.Reflect.Command
public meta import Library.Numerics.Float64.Exp.Program

@[expose] public section

namespace Library.Numerics.Float64.Exp2

verified_compile compiled := [exp2SpecialCase, exp2Core, exp2With, exp10Core, exp10With, exp2,
  exp10]

end Library.Numerics.Float64.Exp2
