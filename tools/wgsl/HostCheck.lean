import Project.WGSL.HostExecution

#print axioms Project.WGSL.HostBinary.encoded
#print axioms Project.WGSL.HostBinary.interface
#print axioms Project.WGSL.HostMemory.upload_word
#print axioms Project.WGSL.HostExecution.completes
#print axioms Project.WGSL.HostExecution.exact
#print axioms Project.WGSL.HostExecution.numerical

def main (args : List String) : IO Unit := do
  let [mode, path] := args | throw (IO.userError "expected --emit or --check and Wasm path")
  let file : System.FilePath := path
  if mode == "--emit" then
    if ← file.pathExists then throw (IO.userError "Wasm output already exists")
    IO.FS.writeBinFile file Project.WGSL.HostBinary.bytes
  else if mode == "--check" then
    unless (← IO.FS.readBinFile file) == Project.WGSL.HostBinary.bytes do
      throw (IO.userError "Wasm bytes differ from the kernel-checked bridge")
    IO.println "WGSL_WASM_HOST_VERIFIED"
  else throw (IO.userError "unknown mode")
