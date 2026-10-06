import Examples.Piecewise.Program
import Examples.Host

/-! The module cases of `piecewise`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Piecewise

open Examples.Host

def piecewiseCases : IO Unit := do
  let chosen : List (Float × Float × Float) :=
    [(1.0, 1.0, 2.0), (0.0, -0.0, 1.0), (0.5, 1.0, 2.0), (3.0, 1.0, 2.0), (2.0, 1.0, 2.0),
     (1.5, 1.0, 2.0), (1.5, 2.0, 1.0), (nan, 1.0, 2.0), (1.0, nan, 2.0), (1.5, 1.0, nan)]
  for (x, lo, hi) in chosen ++ floatTriples do
    line "piecewise" "piecewise" "f64" [fl x, fl lo, fl hi]
      (toString (Examples.Piecewise.piecewise x lo hi).toBits)

def cases : IO Unit := do
  piecewiseCases

end Examples.Piecewise
