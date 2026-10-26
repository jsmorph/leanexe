import Lean
import LeanExe.Native.Subset

open Lean

/-- Prints whether the `Wasm.Module` constant `constName` of `moduleName` is in the subset that
the translator to C accepts, and otherwise the first part outside it; fails in that case. -/
unsafe def check (moduleName constName : Name) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules
    #[{ module := moduleName, importAll := false, isExported := true, isMeta := false }] {}
  let module_ ← IO.ofExcept <| env.evalConst Wasm.Module {} constName
  match LeanExe.Native.violation module_ with
  | none =>
      IO.println s!"{constName}: in the subset"
      pure 0
  | some reason =>
      IO.println s!"{constName}: {reason}"
      pure 1

unsafe def main : List String → IO UInt32
  | [moduleText, constText] => check moduleText.toName constText.toName
  | _ => throw <| IO.userError "usage: Subset.lean <module> <constant>"
