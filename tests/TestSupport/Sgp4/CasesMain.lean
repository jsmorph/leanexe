import TestSupport.Sgp4.Cases

/-! The cases of the module `sgp4` alone, for `tests/verified/run.sh --cases sgp4`.  With the
argument `--states`, it serves `tests/sgp4/reference.py`. -/

def main (args : List String) : IO Unit :=
  if args == ["--states"] then TestSupport.Sgp4.Cases.states
  else TestSupport.Sgp4.Cases.cases
