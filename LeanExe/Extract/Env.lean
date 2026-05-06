import Lean

open Lean

namespace LeanExe.Extract.Env

def parseName (s : String) : Name :=
  s.splitOn "." |>.foldl
    (fun acc part => if part.isEmpty then acc else Name.str acc part)
    .anonymous

def displayName (n : Name) : String :=
  n.toString (escape := false)

def rootName (n : Name) : Name :=
  n.getRoot

def rootString (n : Name) : String :=
  displayName n.getRoot

def loadEnvironment (moduleName : Name) : IO Environment := do
  let cwd ← IO.currentDir
  let projectLean := cwd / ".lake" / "build" / "lib" / "lean"
  initSearchPath (← findSysroot) [projectLean, cwd]
  importModules #[{ module := moduleName, importAll := false, isExported := true, isMeta := false }] {}

end LeanExe.Extract.Env
