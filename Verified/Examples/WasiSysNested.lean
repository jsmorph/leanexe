import Verified.Wasi

/-! A command that writes a file with the iovec calls, reads it back, and polls a clock and the
file.  `main` opens the file `n` under `Handle.preopened` with `withOpen`, created and truncated,
and in the bracket's body writes `abcdef` with `fdWrite`, writes `XY` at offset 6 with `fdPwrite`,
reads up to 16 bytes at offset 0 with `fdPread`, which gives `abcdefXY`, and up to 16 bytes from
the position that the first write left with `fdRead`, which gives `XY`, and writes both to stdout.
It then polls the monotonic clock with timeout 0 with `pollClock` and, after `fdSeek` moves the
position back to 0, the file's readiness to read with `pollRead`, with a monotonic timeout of one
second, and writes the count and the first event's userdata, error, type, `nbytes`, and flags of
each poll as eight little-endian bytes each.  The bracket closes the file when the body returns,
and `main` then removes the file.  An errno of the open or of a call, the bracket's close
included, ends the run with that errno as its status, and the status is 0 otherwise. -/

namespace Verified.Examples.WasiSysNested

open LeanExe LeanExe.Wasi

/-- The eight little-endian bytes of `word`. -/
def wordBytes (word : UInt64) : Bytes :=
  Bytes.build 8 fun index => word >>> (8 * index)

def main : Action UInt64 := do
  let done ← withOpen .preopened 0 bytes![110] 9 1073741823 1073741823 0
    (fun errno => pure errno) fun file => do
      let written ← fdWrite file bytes![97, 98, 99, 100, 101, 102]
      if written.errno != 0 then
        pure written.errno
      else
        let placed ← fdPwrite file bytes![88, 89] 6
        if placed.errno != 0 then
          pure placed.errno
        else
          let whole ← fdPread file 16 0
          if whole.errno != 0 then
            pure whole.errno
          else
            let rest ← fdRead file 16
            if rest.errno != 0 then
              pure rest.errno
            else
              let _ ← writeStdoutSome whole.bytes
              let _ ← writeStdoutSome rest.bytes
              let clock ← pollClock 1 0 0 0
              if clock.errno != 0 then
                pure clock.errno
              else
                let _ ← writeStdoutSome (wordBytes clock.count)
                let _ ← writeStdoutSome (wordBytes clock.userdata)
                let _ ← writeStdoutSome (wordBytes clock.error)
                let _ ← writeStdoutSome (wordBytes clock.type)
                let _ ← writeStdoutSome (wordBytes clock.nbytes)
                let _ ← writeStdoutSome (wordBytes clock.flags)
                let sought ← fdSeek file 0 0
                if sought.errno != 0 then
                  pure sought.errno
                else
                  let ready ← pollRead file 1 1000000000
                  if ready.errno != 0 then
                    pure ready.errno
                  else
                    let _ ← writeStdoutSome (wordBytes ready.count)
                    let _ ← writeStdoutSome (wordBytes ready.userdata)
                    let _ ← writeStdoutSome (wordBytes ready.error)
                    let _ ← writeStdoutSome (wordBytes ready.type)
                    let _ ← writeStdoutSome (wordBytes ready.nbytes)
                    let _ ← writeStdoutSome (wordBytes ready.flags)
                    pure 0
  if done.1 != 0 then
    pure done.1
  else if done.2 != 0 then
    pure done.2
  else
    pathUnlinkFile .preopened bytes![110]

verified_compile_wasi command (main := main) := [wordBytes, main]

end Verified.Examples.WasiSysNested
