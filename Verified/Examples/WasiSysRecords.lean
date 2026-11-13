import Verified.Wasi

/-! A command that writes the fields of the records of the directory preopened at descriptor 3
and of a file it creates there, each as eight little-endian bytes.  `main` writes the fields of
`fdPrestatGet 3`, `fdFdstatGet 3`, and `fdFilestatGet 3`.  It then creates the file `f` with
`pathOpen` in append mode, sets its size to `2^32 + 5` with `fdFilestatSetSize`, writes the fields
of `fdFdstatGet` and `fdFilestatGet` of the file and of `pathFilestatGet 3 0 "f"`, closes the file,
and removes it.  An errno of a call ends the run with that errno as its status, and the status is 0
otherwise. -/

namespace Verified.Examples.WasiSysRecords

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

def main : Action UInt64 := do
  let prestat ← fdPrestatGet 3
  if prestat.errno != 0 then
    pure prestat.errno
  else
    let _ ← writeStdoutSome (wordBytes prestat.tag)
    let _ ← writeStdoutSome (wordBytes prestat.prNameLen)
    let directory ← fdFdstatGet 3
    if directory.errno != 0 then
      pure directory.errno
    else
      let _ ← writeStdoutSome (wordBytes directory.fsFiletype)
      let _ ← writeStdoutSome (wordBytes directory.fsFlags)
      let _ ← writeStdoutSome (wordBytes directory.fsRightsBase)
      let _ ← writeStdoutSome (wordBytes directory.fsRightsInheriting)
      let status ← fdFilestatGet 3
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
        let opened ← pathOpen 3 0 bytes![102] 1 1073741823 1073741823 1
        if opened.errno != 0 then
          pure opened.errno
        else
          let sized ← fdFilestatSetSize opened.value 4294967301
          if sized != 0 then
            pure sized
          else
            let file ← fdFdstatGet opened.value
            if file.errno != 0 then
              pure file.errno
            else
              let _ ← writeStdoutSome (wordBytes file.fsFiletype)
              let _ ← writeStdoutSome (wordBytes file.fsFlags)
              let _ ← writeStdoutSome (wordBytes file.fsRightsBase)
              let _ ← writeStdoutSome (wordBytes file.fsRightsInheriting)
              let fileStatus ← fdFilestatGet opened.value
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
                let pathStatus ← pathFilestatGet 3 0 bytes![102]
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
                  let closed ← fdClose opened.value
                  if closed != 0 then
                    pure closed
                  else
                    pathUnlinkFile 3 bytes![102]

verified_compile_wasi command (main := main) := [wordBytes, main]

end Verified.Examples.WasiSysRecords
