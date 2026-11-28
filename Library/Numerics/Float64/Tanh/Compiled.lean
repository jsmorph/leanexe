module

public import Library.Numerics.Float64.Tanh.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Tanh

verified_compile compiled := [expm1Kernel, expm1, tanh]

end Library.Numerics.Float64.Tanh
