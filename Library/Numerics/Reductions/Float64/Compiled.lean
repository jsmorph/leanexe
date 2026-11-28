module

public import Library.Numerics.Reductions.Float64.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Reductions.Float64

verified_compile compiled := [total, largest, select, sumRange]

end Library.Numerics.Reductions.Float64
