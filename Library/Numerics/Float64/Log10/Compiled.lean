module

public import Library.Numerics.Float64.Log10.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Log10

verified_compile compiled := [kLog1p, log10]

end Library.Numerics.Float64.Log10
