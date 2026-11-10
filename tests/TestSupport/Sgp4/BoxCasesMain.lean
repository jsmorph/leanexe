import TestSupport.Sgp4.BoxCases

/-! The cases of the module `sgp4box` alone, for `tests/verified/run.sh --cases sgp4box`.  With
the argument `--boxes`, it serves `tests/sgp4/reference.py`. -/

def main (args : List String) : IO Unit :=
  if args == ["--boxes"] then TestSupport.Sgp4.BoxCases.boxes
  else TestSupport.Sgp4.BoxCases.cases
