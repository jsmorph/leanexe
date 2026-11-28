module

public import Examples.ScaledHypot.Program
public import Verified.Reflect.Command

@[expose] public section

/-! The verified compiler's module of `scaledHypot`.  The function allocates nothing, so the generated
`compiled.scaledHypot.implements` states that function 2 computes `scaledHypot` without a trap. -/

namespace Examples.ScaledHypot

verified_compile compiled := [scaledHypot]

end Examples.ScaledHypot
