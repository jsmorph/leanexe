import Demos.Euler.Cases
import Examples.Shape.Cases

/-!
The module cases of `euler` and of `shapes`, which `tests/verified/run.sh` checks through
`tests/modules/run.sh` on the verified `euler` and `sums` modules, one line per case in that
driver's format.  `tests/native/verified.sh` runs them
on the translations.  Run with `lake env lean --run`.
-/

def main : IO Unit := do
  Demos.Euler.cases
  Examples.Shape.cases
