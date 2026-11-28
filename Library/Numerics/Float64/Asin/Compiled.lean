module

public import Library.Numerics.Float64.Asin.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Asin

verified_compile compiled := [asinRatio, asin, acos]

end Library.Numerics.Float64.Asin
