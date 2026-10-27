import TestSupport.Slew.Edges

/-! Writes the host session of the single-cone edge cases and native Lean's results, for
`tests/slew/edges.sh`. -/

def main (args : List String) : IO Unit :=
  match args with
  | [script, expected] => TestSupport.Slew.Edges.write script expected
  | _ => throw (IO.userError "usage: EdgesMain SCRIPT EXPECTED")
