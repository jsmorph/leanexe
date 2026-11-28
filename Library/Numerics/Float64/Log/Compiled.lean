module

public import Library.Numerics.Float64.Log.Program
public import Verified.Reflect.Command
public meta import Library.Numerics.Float64.Log.Program

@[expose] public section

namespace Library.Numerics.Float64.Log

verified_compile compiled := [logNear1, logCore, logWith, log]

end Library.Numerics.Float64.Log
