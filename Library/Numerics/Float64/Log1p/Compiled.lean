module

public import Library.Numerics.Float64.Log1p.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Log1p

verified_compile compiled := [log1pTail, log1p]

end Library.Numerics.Float64.Log1p
