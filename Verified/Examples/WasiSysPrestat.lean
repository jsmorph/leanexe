import Verified.Wasi

/-! A command that reads the name of the preopened directory and then opens a file in it.  `main`
reads the record of the preopened directory with `fdPrestatGet` and its name with
`fdPrestatDirName`.  It then opens the file `p` under `Handle.preopened` with `withOpen`, created
and truncated, and in the bracket's body writes the name to the file with `fdWrite`, reads up to 16
bytes at offset 0 with `fdPread`, and writes them to stdout.  The bracket closes the file when the
body returns, and `main` then removes the file.  An errno of a typed call before `pathUnlinkFile`,
of the open, or of the bracket's close ends the run with that errno as its status.  Otherwise the
status is the errno of `pathUnlinkFile`, and the run does not test the result of its write to
stdout.  The result of `fdPrestatDirName`, a pair of a word and bytes, stays in scope after the
call, so the reflector reads each later operand that is not a variable under a `letPair` of it,
among them the literal 3 of `Handle.preopened` before the open and before `pathUnlinkFile`. -/

namespace Verified.Examples.WasiSysPrestat

open LeanExe LeanExe.Wasi

def main : Action UInt64 := do
  let prestat ← fdPrestatGet .preopened
  if prestat.errno != 0 then
    pure prestat.errno
  else
    let name ← fdPrestatDirName .preopened prestat.prNameLen
    if name.errno != 0 then
      pure name.errno
    else
      let copied ← withOpen .preopened 0 bytes![112] 9 1073741823 1073741823 0
        (fun errno => pure errno) fun file => do
          let written ← fdWrite file name.bytes
          if written.errno != 0 then
            pure written.errno
          else
            let back ← fdPread file 16 0
            if back.errno != 0 then
              pure back.errno
            else
              let _ ← writeStdoutSome back.bytes
              pure 0
      if copied.1 != 0 then
        pure copied.1
      else if copied.2 != 0 then
        pure copied.2
      else
        pathUnlinkFile .preopened bytes![112]

verified_compile_wasi command (main := main) := [main]

end Verified.Examples.WasiSysPrestat
