module

public import Library.Numerics.Filters.Cic.Program
public import Verified.Reflect.Command

@[expose] public section

namespace Library.Numerics.Filters.Cic

verified_compile compiled := [integratePass, decimatePass, combPass, cic]

end Library.Numerics.Filters.Cic
