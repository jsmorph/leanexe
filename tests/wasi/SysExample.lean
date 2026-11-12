import Verified.Examples.WasiSys
import LeanExe.Wasi.NativeCalls

/-! Native runs of the flat call example: its output and status with the native host's calls for
several argument lists, and its status when a call replies with an errno.  The checks of the
Wasmtime runs are in `tests/wasi/sys-example-run.sh`. -/

open LeanExe LeanExe.Wasi

namespace SysExampleTest

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- A host that records the bytes written to stdout and serves the flat calls with `sys`. -/
private def recording (written : IO.Ref ByteArray)
    (sys : Call → List Arg → IO (Transfer (List Bytes))) : NativeHost where
  read _ := pure (.returned 0 Bytes.empty)
  write output bytes := do
    if output == .stdout then written.modify (· ++ bytes.data)
    pure (.returned 0 bytes.size)
  exit _ := pure (.ok ())
  sys := sys

private def word (bytes : ByteArray) (offset : Nat) : UInt64 :=
  (List.range 8).foldr (fun index value => bytes.get! (offset + index) |>.toUInt64 |>.add
    (value <<< 8)) 0

/-- Runs the example with the native host's calls for `arguments` and checks its output: the
argument bytes, the count and size, a clock reading, and 16 random bytes, with status 0. -/
private def expect (arguments : List String) : IO Unit := do
  let written ← IO.mkRef ByteArray.empty
  let outcome ← Verified.Examples.WasiSys.main.run
    (recording written (NativeHost.serve arguments))
  let expected := (NativeHost.argumentBytes arguments).data
  let size := expected.size
  match outcome with
  | .returned status => check (status == 0) s!"{arguments}: status {status}"
  | _ => throw (IO.userError s!"{arguments}: expected a return")
  let output ← written.get
  check (output.size == size + 40) s!"{arguments}: {output.size} bytes written"
  check (output.extract 0 size == expected) s!"{arguments}: wrong argument bytes"
  check (word output size == arguments.length.toUInt64) s!"{arguments}: wrong count"
  check (word output (size + 8) == size.toUInt64) s!"{arguments}: wrong size"
  check (word output (size + 16) != 0) s!"{arguments}: clock reading 0"

/-- Runs the example with flat calls that reply with `errno` to `failing` and as the native host
does otherwise, and checks the status and the bytes written. -/
private def expectErrno (failing : String) (errno : UInt64) (size : Nat) : IO Unit := do
  let written ← IO.mkRef ByteArray.empty
  let sys := fun (call : Call) (args : List Arg) => do
    if call.name == failing then
      pure (.returned errno ((Call.outputSizes call [0, 0] args).map NativeHost.zeros))
    else NativeHost.serve ["prog"] call args
  match ← Verified.Examples.WasiSys.main.run (recording written sys) with
  | .returned status => check (status == errno) s!"{failing}: status {status}"
  | _ => throw (IO.userError s!"{failing}: expected a return")
  check ((← written.get).size == size) s!"{failing}: {(← written.get).size} bytes written"

/-- `args_sizes_get` reports sizes whose block reaches `2^32` bytes, and `args` gives errno 61
without calling `args_get`. -/
private def expectOverflow : IO Unit := do
  let written ← IO.mkRef ByteArray.empty
  let sys := fun (call : Call) (args : List Arg) => do
    if call == .argsSizesGet then
      pure (.returned 0 [NativeHost.littleEndianBytes 4 1073741824,
        NativeHost.littleEndianBytes 4 1])
    else if call == .argsGet then
      throw (IO.userError "args_get after an overflowing size")
    else NativeHost.serve [] call args
  match ← Verified.Examples.WasiSys.main.run (recording written sys) with
  | .returned status => check (status == 61) s!"overflow: status {status}"
  | _ => throw (IO.userError "overflow: expected a return")

def main : IO Unit := do
  for arguments in [[], ["prog"], ["prog", "a", "b c", ""], ["prog", "".pushn 'x' 4096]] do
    expect arguments
  expectErrno "args_sizes_get" 8 0
  expectErrno "args_get" 28 0
  expectErrno "clock_time_get" 8 21
  expectErrno "random_get" 52 29
  expectOverflow
  IO.println "flat call example native cases passed: 9"

end SysExampleTest

def main : IO Unit := SysExampleTest.main
