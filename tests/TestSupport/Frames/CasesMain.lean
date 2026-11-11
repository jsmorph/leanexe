import TestSupport.Frames.Cases

/-! The cases of the module `frames` alone, for `tests/verified/run.sh --cases frames`.  With the
argument `--serve`, it reads the input lines of `tests/frames/oracle.py` and prints the results. -/

def main (args : List String) : IO Unit :=
  if args == ["--serve"] then TestSupport.Frames.Cases.serve
  else TestSupport.Frames.Cases.cases
