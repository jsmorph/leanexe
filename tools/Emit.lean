import Lean
import LeanExe.Encoding
import LeanExe.Encoding.Decode

open Lean

/-- Writes `encode c` for the `Wasm.Module` constant `c` defined in `moduleName`,
after checking that `decode` reads the bytes back as `c`. -/
unsafe def emit (moduleName constName : Name) (path : System.FilePath) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := moduleName, importAll := false, isExported := true, isMeta := false }] {}
  let module_ ← IO.ofExcept <| env.evalConst Wasm.Module {} constName
  let bytes ← IO.ofExcept <| Wasm.Encoding.encode module_
  match Wasm.Encoding.decode bytes with
  | .ok decoded =>
      if toString (repr decoded) != toString (repr module_) then
        throw <| IO.userError s!"{constName}: the encoded bytes decode to a different module"
  | .error error =>
      throw <| IO.userError s!"{constName}: the encoded bytes do not decode: {repr error}"
  IO.FS.writeBinFile path bytes

unsafe def main : List String → IO Unit
  | [moduleText, constText, path] => emit moduleText.toName constText.toName path
  | _ => throw <| IO.userError "usage: Emit.lean <module> <constant> <output.wasm>"
