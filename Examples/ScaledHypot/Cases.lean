import Examples.ScaledHypot.Program
import TestSupport.Host

/-! The module cases of `scaledHypot`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.ScaledHypot

open TestSupport.Host

/-- The inputs of the cases, which the verified compiler's cases also use. -/
def samples : List (Float × Float × Float) :=
  [(3.0, 4.0, 1.0), (3.0, 4.0, 0.0), (0.0, 0.0, 0.0)] ++ floatTriples

def scaledHypotCases : IO Unit := do
  for (x, y, s) in samples do
    line "scaledHypot" "scaledHypot" "f64" [fl x, fl y, fl s]
      (toString (Examples.ScaledHypot.scaledHypot x y s).toBits)

def cases : IO Unit := do
  scaledHypotCases

end Examples.ScaledHypot
