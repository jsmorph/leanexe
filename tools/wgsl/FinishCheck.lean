import Project.WGSL.FinishBinary

#print axioms Project.WGSL.FinishBinary.parsed
#print axioms Project.WGSL.FinishBinary.core_valid
#print axioms Project.WGSL.FinishBinary.artifact_exact

def main (args : List String) : IO Unit := do
  let [mode, path] := args | throw (IO.userError "expected --emit or --check and Wasm path")
  let file : System.FilePath := path
  if mode == "--emit" then
    if ← file.pathExists then throw (IO.userError "Wasm output already exists")
    IO.FS.writeBinFile file Project.WGSL.FinishBinary.bytes
  else if mode == "--check" then
    unless (← IO.FS.readBinFile file) == Project.WGSL.FinishBinary.bytes do
      throw (IO.userError "Wasm bytes differ from the kernel-checked bias addition")
    IO.println "WGSL_FINISH_WASM_VERIFIED"
  else throw (IO.userError "unknown mode")
