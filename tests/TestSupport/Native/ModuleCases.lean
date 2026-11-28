module

public import Demos.Euler.Cases
public import Examples.Shape.Cases
public meta import Demos.Euler.Cases
public meta import Examples.Shape.Cases

@[expose] public section

/-!
The module cases of `euler` and of `shapes`, which `tests/verified/run.sh` checks through
`tests/modules/run.sh` on the verified `euler` and `sums` modules, one line per case in that
driver's format.  `tests/native/verified.sh` runs them
on the translations.  Run with `lake env lean --run`.
-/

def main : IO Unit := do
  Demos.Euler.cases
  Examples.Shape.cases
