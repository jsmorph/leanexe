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
    let _ ← writeStdoutSome (wordBytes prestat.tag)
    let _ ← writeStdoutSome (wordBytes prestat.prNameLen)
    let directory ← fdFdstatGet .preopened
    if directory.errno != 0 then
      pure directory.errno
    else
      let _ ← writeStdoutSome (wordBytes directory.fsFiletype)
      let _ ← writeStdoutSome (wordBytes directory.fsFlags)
      let _ ← writeStdoutSome (wordBytes directory.fsRightsBase)
      let _ ← writeStdoutSome (wordBytes directory.fsRightsInheriting)
      let status ← fdFilestatGet .preopened
      if status.errno != 0 then
        pure status.errno
      else
        let _ ← writeStdoutSome (wordBytes status.dev)
        let _ ← writeStdoutSome (wordBytes status.ino)
        let _ ← writeStdoutSome (wordBytes status.filetype)
        let _ ← writeStdoutSome (wordBytes status.nlink)
        let _ ← writeStdoutSome (wordBytes status.size)
        let _ ← writeStdoutSome (wordBytes status.atim)
        let _ ← writeStdoutSome (wordBytes status.mtim)
        let _ ← writeStdoutSome (wordBytes status.ctim)
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
                let _ ← writeStdoutSome (wordBytes fileFlags.fsFiletype)
                let _ ← writeStdoutSome (wordBytes fileFlags.fsFlags)
                let _ ← writeStdoutSome (wordBytes fileFlags.fsRightsBase)
                let _ ← writeStdoutSome (wordBytes fileFlags.fsRightsInheriting)
                let fileStatus ← fdFilestatGet file
                if fileStatus.errno != 0 then
                  pure fileStatus.errno
                else
                  let _ ← writeStdoutSome (wordBytes fileStatus.dev)
                  let _ ← writeStdoutSome (wordBytes fileStatus.ino)
                  let _ ← writeStdoutSome (wordBytes fileStatus.filetype)
                  let _ ← writeStdoutSome (wordBytes fileStatus.nlink)
                  let _ ← writeStdoutSome (wordBytes fileStatus.size)
                  let _ ← writeStdoutSome (wordBytes fileStatus.atim)
                  let _ ← writeStdoutSome (wordBytes fileStatus.mtim)
                  let _ ← writeStdoutSome (wordBytes fileStatus.ctim)
                  let pathStatus ← pathFilestatGet .preopened 0 bytes![102]
                  if pathStatus.errno != 0 then
                    pure pathStatus.errno
                  else
                    let _ ← writeStdoutSome (wordBytes pathStatus.dev)
                    let _ ← writeStdoutSome (wordBytes pathStatus.ino)
                    let _ ← writeStdoutSome (wordBytes pathStatus.filetype)
                    let _ ← writeStdoutSome (wordBytes pathStatus.nlink)
                    let _ ← writeStdoutSome (wordBytes pathStatus.size)
                    let _ ← writeStdoutSome (wordBytes pathStatus.atim)
                    let _ ← writeStdoutSome (wordBytes pathStatus.mtim)
                    let _ ← writeStdoutSome (wordBytes pathStatus.ctim)
                    pure 0
        if written.1 != 0 then
          pure written.1
        else if written.2 != 0 then
          pure written.2
        else
          pathUnlinkFile .preopened bytes![102]

verified_compile_wasi command (main := main) := [wordBytes, main]

end Verified.Examples.WasiSysRecords
