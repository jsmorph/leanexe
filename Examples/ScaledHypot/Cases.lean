import Examples.ScaledHypot.Program
import Examples.Host

/-! The module cases of `scaledHypot`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.ScaledHypot

open Examples.Host

def scaledHypotCases : IO Unit := do
  for (x, y, s) in [(3.0, 4.0, 1.0), (3.0, 4.0, 0.0), (0.0, 0.0, 0.0)] ++ floatTriples do
    line "scaledHypot" "scaledHypot" "f64" [fl x, fl y, fl s]
      (toString (Examples.ScaledHypot.scaledHypot x y s).toBits)

def cases : IO Unit := do
  scaledHypotCases

end Examples.ScaledHypot
