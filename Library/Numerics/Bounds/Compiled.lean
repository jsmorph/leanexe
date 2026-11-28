module

public import Library.Numerics.Bounds.Program
public import Verified.Reflect.Command
public import Library.Numerics.Bounds.Encoding

@[expose] public section

namespace Library.Numerics.Bounds

verified_compile compiled := [absBits, finite, nextUpBits, nextDownBits, endpoint, outAdd, outSub, outMul, outDiv, outSqrt]

end Library.Numerics.Bounds
