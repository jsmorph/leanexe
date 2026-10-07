import Verified.Reflect.Command

/-! The first program of the verified compiler: `a * b + c * c - 7` on 64-bit words.  The
reflector writes the source function, proves that it means `poly`, and states that the module's
bytes compute `poly`. -/

namespace Verified.Examples.Poly

def poly (a b c : UInt64) : UInt64 := a * b + c * c - 7

verified_compile compiled := [poly]

end Verified.Examples.Poly
