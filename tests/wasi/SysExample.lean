import Verified.Examples.WasiSys
import LeanExe.Wasi.NativeCalls

/-! Native runs of the flat call example: its output and status with the native host's calls for
several argument lists, its status when a call replies with an errno, and `args` at its size test
and after an errno of `args_get`.  The checks of the Wasmtime runs are in
`tests/wasi/sys-example-run.sh`. -/

open LeanExe LeanExe.Wasi

namespace SysExampleTest

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- A host that records the bytes written to stdout and serves the flat calls with `sys`. -/
private def recording (written : IO.Ref ByteArray)
    (sys : Call → List Arg → IO (Transfer (List Bytes))) : NativeHost where
  read _ := pure (.returned 0 Bytes.empty)
  write output bytes := do
    match output with
    | .stdout => written.modify (· ++ bytes.data)
    | .stderr => pure ()
    pure (.returned 0 bytes.size)
  exit _ := pure (.ok ())
  sys := sys

private def word (bytes : ByteArray) (offset : Nat) : UInt64 :=
  (List.range 8).foldr (fun index value => bytes.get! (offset + index) |>.toUInt64 |>.add
    (value <<< 8)) 0

/-- Runs the example with the native host's calls for `arguments` and checks its output: the
argument bytes, the count and size, a realtime reading within an hour of the system clock, a
monotonic reading below `10^17` ns, and 16 random bytes, with status 0. -/
private def expect (arguments : List String) : IO Unit := do
  let written ← IO.mkRef ByteArray.empty
  let outcome ← Verified.Examples.WasiSys.main.run
    (recording written (NativeHost.serve arguments))
  let now := (← Std.Time.Timestamp.now).toNanosecondsSinceUnixEpoch.val.toNat
  let expected := (NativeHost.argumentBytes arguments).data
  let size := expected.size
  match outcome with
  | .returned status => check (status == 0) s!"{arguments}: status {status}"
  | _ => throw (IO.userError s!"{arguments}: expected a return")
  let output ← written.get
  check (output.size == size + 48) s!"{arguments}: {output.size} bytes written"
  check (output.extract 0 size == expected) s!"{arguments}: wrong argument bytes"
  check (word output size == arguments.length.toUInt64) s!"{arguments}: wrong count"
  check (word output (size + 8) == size.toUInt64) s!"{arguments}: wrong size"
  let wall := (word output (size + 16)).toNat
  check (wall + 3600000000000 ≥ now && wall ≤ now + 3600000000000)
    s!"{arguments}: realtime reading {wall}, system clock {now}"
  check (word output (size + 24) < 100000000000000000)
    s!"{arguments}: monotonic reading {word output (size + 24)}"

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

/-- Flat calls whose `args_sizes_get` reports `count` arguments of `size` bytes and whose
`args_get` replies with errno 28, recording the names of the calls made. -/
private def sizedArgs (calls : IO.Ref (Array String)) (count size : UInt64) (call : Call)
    (args : List Arg) : IO (Transfer (List Bytes)) := do
  calls.modify (·.push call.name)
  if call == .argsSizesGet then
    pure (.returned 0 [NativeHost.littleEndianBytes 4 count, NativeHost.littleEndianBytes 4 size])
  else if call == .argsGet then
    pure (.returned 28 [Bytes.empty])
  else NativeHost.serve [] call args

/-- `args` at its size test: sizes whose block, `size + 4 · count + 3` bytes, reaches `2^32` give
errno 61 without `args_get`, and sizes one byte smaller reach `args_get`, whose errno leaves count
0, size 0, and no bytes. -/
private def expectArgsLimit : IO Unit := do
  let calls ← IO.mkRef #[]
  let written ← IO.mkRef ByteArray.empty
  match ← args.run (recording written (sizedArgs calls 1073741823 1)) with
  | .returned result =>
    check (result.errno == 61 && result.count == 0 && result.size == 0 &&
      result.bytes.size == 0) "args at 2^32: wrong result"
  | _ => throw (IO.userError "args at 2^32: expected a return")
  check ((← calls.get) == #["args_sizes_get"]) s!"args at 2^32: calls {← calls.get}"
  calls.set #[]
  match ← args.run (recording written (sizedArgs calls 1073741823 0)) with
  | .returned result =>
    check (result.errno == 28 && result.count == 0 && result.size == 0 &&
      result.bytes.size == 0) "args below 2^32: wrong result"
  | _ => throw (IO.userError "args below 2^32: expected a return")
  check ((← calls.get) == #["args_sizes_get", "args_get"]) s!"args below 2^32: calls {← calls.get}"

def main : IO Unit := do
  for arguments in [[], ["prog"], ["prog", "a", "b c", ""], ["prog", "".pushn 'x' 4096]] do
    expect arguments
  expectErrno "args_sizes_get" 8 0
  expectErrno "args_get" 28 0
  expectErrno "clock_time_get" 8 21
  expectErrno "random_get" 52 37
  expectArgsLimit
  IO.println "flat call example native cases passed: 10"

end SysExampleTest

def main : IO Unit := SysExampleTest.main
