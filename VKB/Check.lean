import Lean

open Lean

/-- Reads every entry under `entries`, imports the modules the entries list, and returns one
message for each listed declaration or example that the imported environment lacks and for each
entry whose `id` differs from its directory name.  An entry without a `README.md`, an entry whose
JSON does not parse, or a module that does not exist raises an error. -/
def problems (entries : System.FilePath) : IO (Array String) := do
  initSearchPath (← findSysroot)
  let mut modules : Array Name := #[]
  let mut listed : Array (String × Name) := #[]
  let mut found : Array String := #[]
  for dir in ← entries.readDir do
    unless ← (dir.path / "README.md").pathExists do
      throw <| IO.userError s!"{dir.path}: missing README.md"
    let json ← IO.ofExcept <| Json.parse (← IO.FS.readFile (dir.path / "entry.json"))
    let id ← IO.ofExcept <| json.getObjValAs? String "id"
    unless id == dir.fileName do
      found := found.push s!"{dir.fileName}: id {id} differs from the directory name"
    modules := modules ++ (← IO.ofExcept <| json.getObjValAs? (Array String) "modules").map
      String.toName
    for field in ["declarations", "examples"] do
      listed := listed ++ (← IO.ofExcept <| json.getObjValAs? (Array String) field).map
        fun decl => (id, decl.toName)
  let env ← importModules
    (modules.map fun module => { module, importAll := false, isExported := true, isMeta := false })
    {}
  for (id, decl) in listed do
    unless env.contains decl do
      found := found.push s!"{id}: {decl} does not exist"
  return found

def main (args : List String) : IO UInt32 := do
  let found ← problems (args.headD "VKB/entries")
  for message in found do
    IO.eprintln message
  return if found.isEmpty then 0 else 1
