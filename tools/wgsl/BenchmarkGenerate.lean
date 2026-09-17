import LeanExe.WGSL.Generate
import LeanExe.WGSL.Profile

open LeanExe.WGSL

/-- Benchmark candidates use the same supported GEMM definition. Every emitted
artifact still passes the independent package gate before native execution. -/
def main (args : List String) : IO Unit := do
  let [directory, rows, x, y] := args
    | throw (IO.userError "expected OUTPUT_DIR ROWS WORKGROUP_X WORKGROUP_Y")
  let some rows := rows.toNat? | throw (IO.userError "invalid rows")
  let some workgroupX := x.toNat? | throw (IO.userError "invalid workgroup x")
  let some workgroupY := y.toNat? | throw (IO.userError "invalid workgroup y")
  unless rows = 1 || rows = 3 do throw (IO.userError "benchmark supports one or three rows")
  let candidate := gemmCandidate { rows, cols := 256, inner := 4, workgroupX, workgroupY }
  let kernel ← match lowerCandidate candidate with
    | .ok kernel => pure kernel
    | .error message => throw (IO.userError message)
  let directory : System.FilePath := directory
  let shader := directory / "kernel.wgsl"
  let manifest := directory / "manifest.json"
  if (← shader.pathExists) || (← manifest.pathExists) then
    throw (IO.userError "output artifact already exists")
  IO.FS.createDirAll directory
  IO.FS.writeFile shader kernel.source
  IO.FS.writeFile manifest (renderManifest kernel restrictedProfileId profileRevision)
  IO.println s!"Generated supported GEMM candidate {rows}×256×4 with workgroup {workgroupX}×{workgroupY}"
