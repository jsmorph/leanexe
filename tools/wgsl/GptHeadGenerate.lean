import Project.WGSL.GptHead
import LeanExe.WGSL.Profile

open LeanExe.WGSL

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected fresh output directory")
  let kernel ← match lowerCandidate Project.WGSL.GptHead.candidate with
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
  IO.println s!"Generated the selected GPT vocabulary projection: {shader}"
