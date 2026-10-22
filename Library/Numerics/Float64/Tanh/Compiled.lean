import Library.Numerics.Float64.Tanh.Program
import Verified.Reflect.Command

namespace Library.Numerics.Float64.Tanh

verified_compile compiled := [expm1Kernel, expm1, tanh]

end Library.Numerics.Float64.Tanh
