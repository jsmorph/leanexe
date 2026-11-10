import Verified.Wasi

/-! A command that copies its standard input to its standard output through one buffer.  `main`
reads the input with `readAll limit`, writes the bytes that it returned, continuing after short
writes, and returns 0 when the input held at most `limit` bytes and 1 when it held more.  A read
errno is returned before any write, and a write errno ends the run with that status. -/

namespace Verified.Examples.WasiReadAll

open LeanExe LeanExe.Wasi

def limit : UInt64 := 1000000

/-- The bytes of `bytes` from `start` on. -/
def suffix (bytes : Bytes) (start : UInt64) : Bytes :=
  Bytes.build (bytes.size - start) fun i => bytes.get (start + i)

/-- Writes `bytes` to stdout, continuing after short writes, and exits with the errno of a write
that fails. -/
def writeAll (bytes : Bytes) : Action UInt64 :=
  loop (bytes.size + 1) 0 (fun _ written => written < bytes.size) fun _ written => do
    let reply ← writeStdoutSome (suffix bytes written)
    if reply.errno != 0 then exit reply.errno else pure (written + reply.count)

def main : Action UInt64 := do
  let input ← readAll limit
  if input.errno != 0 then
    pure input.errno
  else
    let _ ← writeAll input.bytes
    if limit < input.bytes.size then pure 1 else pure 0

verified_compile_wasi command (main := main) := [suffix, writeAll, main]

end Verified.Examples.WasiReadAll
