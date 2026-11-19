import Verified.Wasi

/-! A command that reads the name of the preopened directory and then opens a file in it.  `main`
reads the record of the preopened directory with `fdPrestatGet` and its name with
`fdPrestatDirName` into a buffer of the name's length.  It then opens the file `p` under
`Handle.preopened` with `withOpen`, created and truncated, and in the bracket's body writes the name
to the file with `fdWrite`, reads up to 16 bytes at offset 0 into a buffer of 16 bytes with
`fdPread`, and writes the bytes read to stdout.  The bracket closes the file when the
body returns, and `main` then removes the file.  An errno of a typed call before `pathUnlinkFile`,
of the open, or of the bracket's close ends the run with that errno as its status.  Otherwise the
status is the errno of `pathUnlinkFile`, and the run does not test the result of its write to
stdout.  The name's buffer stays in scope after the call, through the bracket's write. -/

namespace Verified.Examples.WasiSysPrestat

open LeanExe LeanExe.Wasi

/-- The first `count` bytes of `buffer`: the bytes that a fill placed from the window's start. -/
def filled (buffer : Bytes) (count : UInt64) : Bytes :=
  Bytes.build count fun index => buffer.get index

def main : Action UInt64 := do
  let prestat ← fdPrestatGet .preopened
  if prestat.errno != 0 then
    pure prestat.errno
  else
    let name ← fdPrestatDirName .preopened (Bytes.build prestat.prNameLen fun _ => 0) 0
      prestat.prNameLen
    if name.errno != 0 then
      pure name.errno
    else
      let copied ← withOpen .preopened 0 bytes![112] 9 1073741823 1073741823 0
        (fun errno => pure errno) fun file => do
          let written ← fdWrite file name.buffer 0 name.count
          if written.errno != 0 then
            pure written.errno
          else
            let back ← fdPread file (Bytes.build 16 fun _ => 0) 0 16 0
            if back.errno != 0 then
              pure back.errno
            else
              let _ ← writeStdoutSome (filled back.buffer back.count)
              pure 0
      if copied.1 != 0 then
        pure copied.1
      else if copied.2 != 0 then
        pure copied.2
      else
        pathUnlinkFile .preopened bytes![112]

verified_compile_wasi command (main := main) := [filled, main]

end Verified.Examples.WasiSysPrestat
