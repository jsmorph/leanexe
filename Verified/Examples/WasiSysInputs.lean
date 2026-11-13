import Verified.Wasi

/-! A command with flat calls that take inputs.  `main` creates the directory `d` in the directory
preopened at descriptor 3, with the path as an argument that is not a variable, removes it with the
path in a variable, and removes it again with the same variable, which gives errno 44 (`noent`).  An
errno other than these ends the run with that errno as its status, the last one plus 1000, and the
status is 0 otherwise.  The path variable stays live across the first removal and dies at the
second, after which the command releases it. -/

namespace Verified.Examples.WasiSysInputs

open LeanExe LeanExe.Wasi

def main : Action UInt64 := do
  let created ← pathCreateDirectory 3 bytes![100]
  if created != 0 then
    pure created
  else
    let path := bytes![100]
    let removed ← pathRemoveDirectory 3 path
    if removed != 0 then
      pure removed
    else
      let again ← pathRemoveDirectory 3 path
      if again == 44 then pure 0 else pure (again + 1000)

verified_compile_wasi command (main := main) := [main]

end Verified.Examples.WasiSysInputs
