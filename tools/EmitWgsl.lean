import Lean
import LeanExe.WGSL.Parse

open Lean

/-- Writes the text of the kernel constant `c` defined in `moduleName`, after checking that the
parser reads the text back as `c`. -/
unsafe def emit (moduleName constName : Name) (path : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := moduleName, importAll := false, isExported := true, isMeta := false }] {}
  let kernel ← IO.ofExcept <| env.evalConst LeanExe.WGSL.Module {} constName
  let text := kernel.print
  match LeanExe.WGSL.Module.parse text with
  | some parsed =>
      if toString (repr parsed) != toString (repr kernel) then
        throw <| IO.userError s!"{constName}: the text parses to a different kernel"
  | none => throw <| IO.userError s!"{constName}: the text does not parse"
  IO.FS.writeFile path text

unsafe def main : List String → IO Unit
  | [moduleText, constText, path] => emit moduleText.toName constText.toName path
  | _ => throw <| IO.userError "usage: Emit.lean <module> <constant> <output.wgsl>"
