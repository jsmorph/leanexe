module

public import Verified.Wasi
public import LeanExe.Wasi.WriteAll

@[expose] public section

/-! A command that copies its standard input to its standard output through one buffer.  `main`
reads the input with `readAll limit`, writes the bytes that it returned with `writeAll` of
`LeanExe/Wasi/WriteAll.lean`, continuing after short writes, and returns 0 when the input held at
most `limit` bytes and 1 when it held more.  A read errno is returned before any write, and a write
errno ends the run with that status. -/

namespace Verified.Examples.WasiReadAll

open LeanExe LeanExe.Wasi

def limit : UInt64 := 1000000

def main : Action UInt64 := do
  let input ← readAll limit
  if input.errno != 0 then
    pure input.errno
  else
    let _ ← writeAll input.bytes 0 input.bytes.size
    if limit < input.bytes.size then pure 1 else pure 0

verified_compile_wasi command (main := main) := [writeAll, main]

end Verified.Examples.WasiReadAll
