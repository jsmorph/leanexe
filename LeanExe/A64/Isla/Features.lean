module

public import LeanExe.Base
public import Lean

@[expose] public section

/-!
The settings of a processor profile's `features` file and their reader, in a module of their own so
that `LeanExe.A64.Isla.Profile` can read them in its elaborator `isla_features%`, at the meta phase,
and use them in its definitions as ordinary code.
-/

namespace LeanExe.A64.Isla

/-- The settings of a profile's `features` file: `settings` holds the pair `(NAME, b)` of each line
`NAME=b` in order, which `traces.sh` passes as `-I NAME=b`, and `impl` the values `b` of the lines
whose names begin with `FEAT_`, in order. -/
structure Features where
  settings : List (String × Bool)
  impl : List Bool
  deriving Lean.ToExpr

/-- The settings of the text `s` of a `features` file, whose nonempty lines are `NAME=true` or
`NAME=false`. -/
def parseFeatures (s : String) : Except String Features := do
  let settings ← ((s.splitOn "\n").filter (· ≠ "")).mapM fun l =>
    match l.splitOn "=" with
    | [n, "true"] => .ok (n, true)
    | [n, "false"] => .ok (n, false)
    | _ => .error s!"bad setting {l}"
  return ⟨settings,
    settings.filterMap fun (n, b) => if n.startsWith "FEAT_" then some b else none⟩

end LeanExe.A64.Isla
