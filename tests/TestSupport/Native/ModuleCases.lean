import Demos.Euler.Cases
import Examples.Shape.Cases

/-!
The module cases of `tests/modules/Cases.lean` for the two modules of the `tests/verified` corpus
that `tests/verified/run.sh` checks through `tests/modules/run.sh`: `euler`, and `shapes` on the
`sums` module, one line per case in that driver's format.  `tests/native/verified.sh` runs them
on the translations.  Run with `lake env lean --run`.
-/

def main : IO Unit := do
  Demos.Euler.cases
  Examples.Shape.cases
