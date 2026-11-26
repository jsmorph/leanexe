module

public import Library.Numerics.Float64.Log2.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Float64.Log2

verified_compile compiled := [log2Near1, log2Core, log2With, log2]

end Library.Numerics.Float64.Log2
