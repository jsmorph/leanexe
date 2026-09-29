import Lean

open Lean

/-- Reads every entry under `entries`, imports the modules the entries list, and
returns the entries' declarations that the imported environment lacks.  An
entry whose JSON does not parse, or a module that does not exist, raises an
error. -/
def missingDeclarations (entries : System.FilePath) : IO (Array (String × Name)) := do
  initSearchPath (← findSysroot)
  let mut modules : Array Name := #[]
  let mut listed : Array (String × Name) := #[]
  for dir in ← entries.readDir do
    unless ← (dir.path / "README.md").pathExists do
      throw <| IO.userError s!"{dir.path}: missing README.md"
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile (dir.path / "entry.json"))
    let id ← IO.ofExcept <| json.getObjValAs? String "id"
    modules := modules ++ (← IO.ofExcept <| json.getObjValAs? (Array String) "modules").map
      String.toName
    listed := listed ++ (← IO.ofExcept <| json.getObjValAs? (Array String) "declarations").map
      fun decl => (id, decl.toName)
  let env ← importModules
    (modules.map fun module => { module, importAll := false, isExported := true, isMeta := false })
    {}
  return listed.filter fun (_, decl) => !env.contains decl

def main (args : List String) : IO UInt32 := do
  let entries := args.headD "ltg/entries"
  let missing ← missingDeclarations entries
  for (id, decl) in missing do
    IO.eprintln s!"{id}: {decl} does not exist"
  return if missing.isEmpty then 0 else 1
