import Verified.Wasi

/-! A command that writes the fields of the records of the preopened directory and of a file it
creates there, each as eight little-endian bytes.  `main` writes the fields of
`fdPrestatGet .preopened`, `fdFdstatGet .preopened`, and `fdFilestatGet .preopened`.  It then
opens the file `f` with `withOpen`, created in append mode, and in the bracket's body sets its size
to `2^32 + 5` with `fdFilestatSetSize`, writes the fields of `fdFdstatGet` and `fdFilestatGet` of
the file and of `pathFilestatGet .preopened 0 "f"`, and returns 0; the bracket closes the file
when the body returns.  After the bracket it removes the file.  An errno of the open or of a call,
the bracket's close included, ends the run with that errno as its status, and the status is 0
otherwise. -/

namespace Verified.Examples.WasiSysRecords

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

def main : Action UInt64 := do
  let prestat ← fdPrestatGet .preopened
  if prestat.errno != 0 then
    pure prestat.errno
  else
    let _ ← writeStdout (wordBytes prestat.tag) 0 8
    let _ ← writeStdout (wordBytes prestat.prNameLen) 0 8
    let directory ← fdFdstatGet .preopened
    if directory.errno != 0 then
      pure directory.errno
    else
      let _ ← writeStdout (wordBytes directory.fsFiletype) 0 8
      let _ ← writeStdout (wordBytes directory.fsFlags) 0 8
      let _ ← writeStdout (wordBytes directory.fsRightsBase) 0 8
      let _ ← writeStdout (wordBytes directory.fsRightsInheriting) 0 8
      let status ← fdFilestatGet .preopened
      if status.errno != 0 then
        pure status.errno
      else
        let _ ← writeStdout (wordBytes status.dev) 0 8
        let _ ← writeStdout (wordBytes status.ino) 0 8
        let _ ← writeStdout (wordBytes status.filetype) 0 8
        let _ ← writeStdout (wordBytes status.nlink) 0 8
        let _ ← writeStdout (wordBytes status.size) 0 8
        let _ ← writeStdout (wordBytes status.atim) 0 8
        let _ ← writeStdout (wordBytes status.mtim) 0 8
        let _ ← writeStdout (wordBytes status.ctim) 0 8
        let written ← withOpen .preopened 0 bytes![102] 1 1073741823 1073741823 1
          (fun errno => pure errno) fun file => do
            let sized ← fdFilestatSetSize file 4294967301
            if sized != 0 then
              pure sized
            else
              let fileFlags ← fdFdstatGet file
              if fileFlags.errno != 0 then
                pure fileFlags.errno
              else
                let _ ← writeStdout (wordBytes fileFlags.fsFiletype) 0 8
                let _ ← writeStdout (wordBytes fileFlags.fsFlags) 0 8
                let _ ← writeStdout (wordBytes fileFlags.fsRightsBase) 0 8
                let _ ← writeStdout (wordBytes fileFlags.fsRightsInheriting) 0 8
                let fileStatus ← fdFilestatGet file
                if fileStatus.errno != 0 then
                  pure fileStatus.errno
                else
                  let _ ← writeStdout (wordBytes fileStatus.dev) 0 8
                  let _ ← writeStdout (wordBytes fileStatus.ino) 0 8
                  let _ ← writeStdout (wordBytes fileStatus.filetype) 0 8
                  let _ ← writeStdout (wordBytes fileStatus.nlink) 0 8
                  let _ ← writeStdout (wordBytes fileStatus.size) 0 8
                  let _ ← writeStdout (wordBytes fileStatus.atim) 0 8
                  let _ ← writeStdout (wordBytes fileStatus.mtim) 0 8
                  let _ ← writeStdout (wordBytes fileStatus.ctim) 0 8
                  let pathStatus ← pathFilestatGet .preopened 0 bytes![102]
                  if pathStatus.errno != 0 then
                    pure pathStatus.errno
                  else
                    let _ ← writeStdout (wordBytes pathStatus.dev) 0 8
                    let _ ← writeStdout (wordBytes pathStatus.ino) 0 8
                    let _ ← writeStdout (wordBytes pathStatus.filetype) 0 8
                    let _ ← writeStdout (wordBytes pathStatus.nlink) 0 8
                    let _ ← writeStdout (wordBytes pathStatus.size) 0 8
                    let _ ← writeStdout (wordBytes pathStatus.atim) 0 8
                    let _ ← writeStdout (wordBytes pathStatus.mtim) 0 8
                    let _ ← writeStdout (wordBytes pathStatus.ctim) 0 8
                    pure 0
        if written.1 != 0 then
          pure written.1
        else if written.2 != 0 then
          pure written.2
        else
          pathUnlinkFile .preopened bytes![102]

verified_compile_wasi command (main := main) := [wordBytes, main]

end Verified.Examples.WasiSysRecords
