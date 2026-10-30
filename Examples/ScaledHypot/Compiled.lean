import Examples.ScaledHypot.Program
import Verified.Reflect.Command

/-! The verified compiler's module of `scaledHypot`.  The function allocates nothing, so the generated
`compiled.scaledHypot.implements` states that function 2 computes `scaledHypot` without a trap. -/

namespace Examples.ScaledHypot

verified_compile compiled := [scaledHypot]

end Examples.ScaledHypot
