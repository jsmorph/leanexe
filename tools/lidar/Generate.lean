import LeanExe.WGSL.Lidar
import LeanExe.WGSL.LidarOblique
import LeanExe.WGSL.LidarInterval
import LeanExe.WGSL.LidarSummary
import LeanExe.WGSL.UIntCertificate
import LeanExe.Extract.Arithmetic
import LeanExe.Wasm.Binary

open LeanExe.WGSL

def certificate (name : String) (kernelName : String) (kernel : UInt.Expr) : IO String := do
  let (out, code) := kernel.emit.run {}
  let mut text := "import LeanExe.WGSL.LidarInterval\nimport LeanExe.WGSL.UIntComposition\nimport LeanExe.WGSL.LidarSummary\nset_option maxRecDepth 2048\nset_option maxHeartbeats 4000000\nnamespace Project.Lidar." ++ name ++ "\nopen LeanExe.WGSL.UInt\ndef state0 : Locals := []\n"
  let mut locals : UInt.Locals := []
  let mut index := 0
  for line in code.lines do
    let some next := UInt.lineStep locals line | throw (IO.userError "line parse failed")
    let some (key,value) := next.head? | throw (IO.userError "missing parsed statement")
    let previous := s!"state{index}"
    index := index+1
    text := text ++ s!"def line{index} : String := " ++ reprStr line ++ "\n" ++
      s!"def value{index} : Expr := " ++ reprStr value ++ "\n" ++
      s!"def state{index} : Locals := (" ++ reprStr key ++ s!",value{index})::{previous}\n" ++
      s!"theorem step{index} : lineStep {previous} line{index} = some state{index} := by decide +kernel\n"
    locals := next
  let names := (List.range index).map (fun i => s!"line{i+1}")
  text := text ++ "def lines : List String := [" ++ String.intercalate "," names ++ "]\n"
  let mut proof := s!"steps_nil state{index}"
  for i in (List.range index).reverse do
    proof := s!"steps_cons step{i+1} ({proof})"
  text := text ++ s!"theorem stepped : steps lines [] = some state{index} :=\n  {proof}\n"
  text := text ++ s!"theorem output : lookup state{index} " ++ reprStr out ++
    s!" = some {kernelName} := by decide +kernel\n" ++
    "def shaderText : String := String.intercalate \"\\n\" (headerLines ++ lines ++ footer " ++ reprStr out ++ ")\n" ++
    s!"theorem certified : Certified shaderText {kernelName} := ⟨lines, state{index}, " ++ reprStr out ++ ", stepped, output, rfl⟩\n" ++
    "#print axioms certified\nend Project.Lidar." ++ name ++ "\n"
  return text

def main (args : List String) : IO Unit := do
  let output := System.FilePath.mk (args.headD "build/lidar/bundle")
  IO.FS.createDirAll output
  let oblique := args[1]? == some "oblique"
  let interval := args[1]? == some "interval"
  let kernel := if interval then LidarInterval.outer else if oblique then LidarOblique.kernel else Lidar.kernel
  let kernelName := if interval then "LeanExe.WGSL.LidarInterval.outer" else if oblique then "LeanExe.WGSL.LidarOblique.kernel" else "LeanExe.WGSL.Lidar.kernel"
  let shader := UInt.shader kernel 4
  IO.FS.writeFile (output / "scan.wgsl") shader
  unless UInt.parse shader == some kernel do
    IO.FS.writeFile (output / "parse-debug.txt") (reprStr (UInt.parse shader))
    throw (IO.userError "generated lidar shader failed independent parsing")
  IO.FS.writeFile (output / "scan.wgsl") shader
  IO.FS.writeFile (output / "Shader.lean") (← certificate "Artifact" kernelName kernel)
  if interval then
    let inner := UInt.shader LidarInterval.inner 4
    unless UInt.parse inner == some LidarInterval.inner do
      throw (IO.userError "generated inner shader failed independent parsing")
    IO.FS.writeFile (output / "inner.wgsl") inner
    IO.FS.writeFile (output / "Inner.lean") (← certificate "InnerArtifact" "LeanExe.WGSL.LidarInterval.inner" LidarInterval.inner)
  let summary := UInt.shader LidarSummary.kernel 4
  unless UInt.parse summary == some LidarSummary.kernel do
    throw (IO.userError "generated summary failed independent parsing")
  IO.FS.writeFile (output / "summary.wgsl") summary
  IO.FS.writeFile (output / "Summary.lean") (← certificate "SummaryArtifact" "LeanExe.WGSL.LidarSummary.kernel" LidarSummary.kernel)
  let env ← LeanExe.Extract.Env.loadEnvironment `LeanExe.Examples.Lidar
  let info := (env.find? `LeanExe.Examples.Lidar.parameters).get!
  IO.FS.writeFile (output / "source-repr.txt") (reprStr info.value!)
  let module ← LeanExe.Extract.Arithmetic.compile "LeanExe.Examples.Lidar" "LeanExe.Examples.Lidar.parameters"
  let some func := module.funcs[0]? | throw (IO.userError "missing controller function")
  let bytes := LeanExe.Wasm.Binary.CoreWasm.moduleBytes module
  IO.FS.writeBinFile (output / "controller.wasm") bytes
  let certificate := "import Project.Compiler.SourceCorrectness\nset_option maxRecDepth 8192\nset_option maxHeartbeats 4000000\nnamespace Project.Lidar.ControllerArtifact\n" ++
    "def source : Lean.Expr := " ++ reprStr info.value! ++ "\n" ++
    "def sourceType : Lean.Expr := " ++ reprStr info.type ++ "\n" ++
    "def func : LeanExe.IR.Func :=\n" ++ reprStr func ++ "\n" ++
    "def bytes : ByteArray := ⟨" ++ reprStr bytes.data ++ "⟩\n" ++
    "theorem extracted : LeanExe.Extract.Core.extractScalarFunc `LeanExe.Examples.Lidar.parameters (some \"parameters\") sourceType source = some func := by cbv\n" ++
    "theorem fits : LeanExe.Wasm.ArithmeticBounds.Fits func \"parameters\" := by decide +kernel\n" ++
    "theorem emitted : LeanExe.Wasm.Binary.CoreWasm.moduleBytes { funcs := #[func] } = bytes := by decide +kernel\n" ++
    "theorem correct : Project.Compiler.ArithmeticModule.Correct Unit source \"parameters\" 4 bytes := by\n  rw [← emitted]\n  exact Project.Compiler.ArithmeticModule.extracted_correct extracted (by decide) fits\n" ++
    "#print axioms correct\nend Project.Lidar.ControllerArtifact\n"
  IO.FS.writeFile (output / "Controller.lean") certificate
  IO.println s!"Generated {shader.utf8ByteSize} shader bytes and controller in {output}"
