module

public import Library.Numerics.Float64.Atan.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Atan

verified_compile compiled := [atan, atan2]

end Library.Numerics.Float64.Atan
