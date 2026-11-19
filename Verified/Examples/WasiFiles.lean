import Verified.Wasi

/-! A command that writes a file in one bracket and reads it back in another, with the functions
that the Linux shim implements.  `main` opens the file `f` under the preopened directory with
`withOpen`, created and truncated with the right to write, and writes `hi` with `fdWrite`.  It then
opens `f` again with the right to read, reads up to 16 bytes into a buffer of 16 bytes with
`fdRead`, and writes the bytes read to stdout.  Each bracket closes the file when its body returns.
Last it reads the record of the preopened directory with `fdPrestatGet` and its name with
`fdPrestatDirName` into a buffer of the name's length and writes the name to stdout.  An errno of the opens or of a call, the brackets' closes included, ends the run with
that errno as its status, and the status is 0 otherwise. -/

namespace Verified.Examples.WasiFiles

open LeanExe LeanExe.Wasi

def main : Action UInt64 := do
  let written ← withOpen .preopened 0 bytes![102] 9 64 0 0
    (fun errno => pure errno) fun file => do
      let sent ← fdWrite file bytes![104, 105] 0 2
      pure sent.errno
  if written.1 != 0 then
    pure written.1
  else if written.2 != 0 then
    pure written.2
  else
    let read ← withOpen .preopened 0 bytes![102] 0 2 0 0
      (fun errno => pure errno) fun file => do
        let got ← fdRead file (Bytes.build 16 fun _ => 0) 0 16
        if got.errno != 0 then
          pure got.errno
        else
          let _ ← writeStdout got.buffer 0 got.count
          pure 0
    if read.1 != 0 then
      pure read.1
    else if read.2 != 0 then
      pure read.2
    else
      let prestat ← fdPrestatGet .preopened
      if prestat.errno != 0 then
        pure prestat.errno
      else
        let name ← fdPrestatDirName .preopened (Bytes.build prestat.prNameLen fun _ => 0) 0
          prestat.prNameLen
        if name.errno != 0 then
          pure name.errno
        else
          let _ ← writeStdout name.buffer 0 name.buffer.size
          pure 0

verified_compile_wasi command (main := main) := [main]

end Verified.Examples.WasiFiles
