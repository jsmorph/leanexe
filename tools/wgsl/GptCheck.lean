import Project.WGSL.GptHiddenArtifact
import Project.WGSL.GptNumerical
import Project.WGSL.GptBundle

open Project.WGSL Project.TinyGpt2

#print axioms GptHiddenArtifact.interface
#print axioms GptHiddenArtifact.exact
#print axioms GptBundle.artifact
#print axioms FinishBinary.artifact_exact
#print axioms GptHead.restricted_exact
#print axioms GptHeadCheckpoint.real_error_uniform

def checkpointBytes : ByteArray := Id.run do
  let mut bytes := ByteArray.empty
  for word in Checkpoint.words do
    for i in [:8] do
      bytes := bytes.push ((word >>> (UInt64.ofNat (8*i))).toUInt8)
  return bytes

def main (args : List String) : IO Unit := do
  match args with
  | ["--emit", directory] =>
      let directory : System.FilePath := directory
      for (name, bytes) in [("hidden.wasm", Project.TinyGpt2Hidden.Artifact.artifactBytes),
          ("finish.wasm", FinishBinary.bytes), ("weights.bin", checkpointBytes)] do
        let target := directory / name
        if ← target.pathExists then throw (IO.userError s!"output exists: {target}")
        IO.FS.writeBinFile target bytes
  | ["--check", hiddenPath, finishPath, weightsPath] =>
      unless (← IO.FS.readBinFile hiddenPath) == Project.TinyGpt2Hidden.Artifact.artifactBytes do
        throw (IO.userError "hidden Wasm bytes differ from the proved artifact")
      unless (← IO.FS.readBinFile finishPath) == FinishBinary.bytes do
        throw (IO.userError "finish Wasm bytes differ from the proved artifact")
      unless (← IO.FS.readBinFile weightsPath) == checkpointBytes do
        throw (IO.userError "weights differ from the proved checkpoint")
      IO.println "WGSL_GPT_ARTIFACTS_VERIFIED"
  | _ => throw (IO.userError "expected --emit DIR or --check HIDDEN FINISH WEIGHTS")
