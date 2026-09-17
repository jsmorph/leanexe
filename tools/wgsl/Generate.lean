import LeanExe.WGSL.Generate
import LeanExe.WGSL.Profile

open LeanExe.WGSL

/-- Emit the supported checked GEMM candidate. Existing artifact paths are
rejected so a second run cannot silently replace earlier execution evidence. -/
def main (args : List String) : IO Unit := do
  let [directory, rows, cols, inner, profile] := args
    | throw (IO.userError "usage: Generate.lean OUTPUT_DIR ROWS COLS INNER separate|fusion")
  let some rows := rows.toNat? | throw (IO.userError "invalid rows")
  let some cols := cols.toNat? | throw (IO.userError "invalid cols")
  let some inner := inner.toNat? | throw (IO.userError "invalid inner dimension")
  let profileId ← match profile with
    | "separate" => pure restrictedProfileId
    | "fusion" => pure fusionProfileId
    | _ => throw (IO.userError "profile must be separate or fusion")
  let kernel ← match lowerCandidate (gemmCandidate { rows, cols, inner }) with
    | .ok kernel => pure kernel
    | .error message => throw (IO.userError message)
  let directory : System.FilePath := directory
  let shader := directory / "kernel.wgsl"
  let manifest := directory / "manifest.json"
  if (← shader.pathExists) || (← manifest.pathExists) then
    throw (IO.userError "output artifact already exists; choose a new output directory")
  IO.FS.createDirAll directory
  IO.FS.writeFile shader kernel.source
  IO.FS.writeFile manifest (renderManifest kernel profileId profileRevision)
  IO.println s!"Generated {shader} and {manifest} ({rows}x{cols}x{inner}, {profileId})"
