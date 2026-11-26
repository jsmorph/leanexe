module

public import Library.Numerics.LinearAlgebra.Float64.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.LinearAlgebra.Float64

verified_compile compiled := [dot, axpy, grid, matVec, matMul, matMulT, add]

end Library.Numerics.LinearAlgebra.Float64
