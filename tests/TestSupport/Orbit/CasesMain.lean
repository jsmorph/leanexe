import TestSupport.Orbit.Cases

/-! The cases of the modules `gibbs` and `lambert`, for `tests/verified/run.sh --cases gibbs` and
`--cases lambert`.  With the argument `--gibbs` or `--lambert`, it serves
`tests/orbit/reference.py`. -/

def main (args : List String) : IO Unit :=
  if args == ["--gibbs"] then TestSupport.Orbit.Cases.gibbs
  else if args == ["--lambert"] then TestSupport.Orbit.Cases.lambert
  else TestSupport.Orbit.Cases.cases
