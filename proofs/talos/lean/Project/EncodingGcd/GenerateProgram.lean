import LeanExe.Extract.Core
import Project.EncodingGcd.Direct

private def inlineRepr {α : Type} [Repr α] (value : α) : String :=
  (repr value).pretty.replace "\n" " "

private def functionSource (index : Nat) (func : Wasm.Function) : String :=
  s!"def func{index}Def : Wasm.Function :=\n" ++ (repr func).pretty ++ "\n"

private def gcdFunctionSource (func : Wasm.Function) : String :=
  "def func0 : Wasm.Program :=\n" ++ (repr func.body).pretty ++ "\n\n" ++
  "def func0Def : Wasm.Function :=\n" ++
  "{ params := " ++ inlineRepr func.params ++
  ", locals := " ++ inlineRepr func.locals ++
  ", body := func0, results := " ++ inlineRepr func.results ++
  ", typeIdx := " ++ inlineRepr func.typeIdx ++ " }\n"

private def moduleSource (module_ : Wasm.Module) : String :=
  "def «module» : Wasm.Module :=\n" ++
  "{ funcs := [func0Def, func1Def, func2Def, func3Def, func4Def],\n" ++
  "  exports := " ++ inlineRepr module_.exports ++ ",\n" ++
  "  memory := (" ++ inlineRepr module_.memory ++ "),\n" ++
  "  globals := " ++ inlineRepr module_.globals ++ ",\n" ++
  "  types := " ++ inlineRepr module_.types ++ ",\n" ++
  "  gcTypes := " ++ inlineRepr module_.gcTypes ++ ",\n" ++
  "  globalExports := " ++ inlineRepr module_.globalExports ++ ",\n" ++
  "  memoryExports := " ++ inlineRepr module_.memoryExports ++ " }\n"

def main (args : List String) : IO Unit := do
  let path ← match args with
    | [path] => pure path
    | _ => throw (IO.userError "expected a Lean output path")
  let ir ← LeanExe.Extract.Core.compile
    "LeanExe.Examples.EncodingGcd" "LeanExe.Examples.EncodingGcd.gcd"
  let module_ ← match Project.EncodingGcd.fromIR ir with
    | .ok module_ => pure module_
    | .error message => throw (IO.userError message)
  let source ← match module_.funcs with
    | [f0, f1, f2, f3, f4] =>
        pure ("/- Generated from LeanExe.Examples.EncodingGcd by GenerateProgram.lean. -/\n\n" ++
          "import Project.TalosPrelude\n\n" ++
          "set_option maxRecDepth 1048576\n\n" ++
          "namespace Project.EncodingGcd\n\n" ++
          "open Wasm\n\n" ++
          gcdFunctionSource f0 ++ "\n" ++
          functionSource 1 f1 ++ "\n" ++
          functionSource 2 f2 ++ "\n" ++
          functionSource 3 f3 ++ "\n" ++
          functionSource 4 f4 ++ "\n" ++
          moduleSource module_ ++ "\n" ++
          "end Project.EncodingGcd\n")
    | _ => throw (IO.userError "expected five compiled functions")
  IO.FS.writeFile path source
