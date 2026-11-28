module

public import Library.Numerics.LinearAlgebra.Binary32.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.LinearAlgebra.Binary32

verified_compile compiled := [scale32, axpyArray32, matVec32, add32, linear32]

end Library.Numerics.LinearAlgebra.Binary32
