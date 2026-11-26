module

public import Library.Numerics.Float64.Pow.Program
public import Verified.Reflect.Command
public meta import Library.Numerics.Float64.Exp.Program
public meta import Library.Numerics.Float64.Pow.Program

@[expose] public section

namespace Library.Numerics.Float64.Pow

verified_compile compiled := [checkint, zeroinfnan, issignaling, powLog, powSpecialCase,
  powExpCore, powExp, powMain, powWith, pow]

end Library.Numerics.Float64.Pow
