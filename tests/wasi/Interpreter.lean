import LeanExe.Wasi.NativeCalls
import LeanExe.Wasi.Sys

open LeanExe LeanExe.Wasi

namespace NativeInterpreterTest

private inductive Call where
  | read (capacity : UInt64)
  | write (fd : UInt64) (bytes : List UInt8)
  | exit (code : UInt64)
  deriving BEq

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def returned [BEq α] (expected : α) : Outcome α → IO Unit
  | .returned value => check (value == expected) "unexpected returned value"
  | _ => throw (IO.userError "expected a normal return")

private def trapped (expected : String) : Outcome α → IO Unit
  | .trapped message => check (message == expected) "unexpected trap"
  | _ => throw (IO.userError "expected a terminal trap")

private def recordHost (calls : IO.Ref (Array Call)) : NativeHost where
  read capacity := do
    calls.modify (·.push (.read capacity))
    pure (.returned 0 Bytes.empty)
  write output bytes := do
    calls.modify (·.push (.write output.fd bytes.data.data.toList))
    pure (.returned 0 bytes.size)
  exit code := do
    calls.modify (·.push (.exit code))
    pure (.ok ())

private def primitives : IO Unit := do
  let calls ← IO.mkRef #[]
  let host := { recordHost calls with
    read := fun capacity => do
      calls.modify (·.push (.read capacity))
      pure (.returned 29 (if capacity == 0 then Bytes.empty else bytes![255]))
    write := fun output bytes => do
      calls.modify (·.push (.write output.fd bytes.data.data.toList))
      pure (.returned (if output = .stderr then 29 else 0) 1) }
  let program : Action (UInt64 × UInt64 × UInt64 × UInt64 × UInt64) := do
    let action := readSome 0
    let _ ← action
    let _ ← action
    let oversized ← readSome 4294967296
    let failed ← readSome 1
    let short ← writeStdoutSome bytes![65, 66]
    let error ← writeStderrSome bytes![67]
    pure (oversized.errno, failed.bytes.size, short.count, error.errno, error.count)
  returned (61, 0, 1, 29, 0) (← program.run host)
  check ((← calls.get) == #[.read 0, .read 0, .read 1,
    .write 1 [65, 66], .write 2 [67]]) "primitive order or overflow rejection"

private def loops : IO Unit := do
  let calls ← IO.mkRef #[]
  let host := recordHost calls
  let step (index state : UInt64) : Action UInt64 := do
    let _ ← writeStdoutSome (Bytes.build 1 (fun _ => index))
    pure (state + 1)
  returned 9 (← (loop 0 9 (fun _ _ => true) step).run host)
  returned 9 (← (loop 18446744073709551615 9 (fun _ _ => false) step).run host)
  returned 3 (← (loop 4 0 (fun index _ => index < 3) step).run host)
  check ((← calls.get) == #[.write 1 [0], .write 1 [1], .write 1 [2]])
    "loop count, test, or index"

private def terminals : IO Unit := do
  let calls ← IO.mkRef #[]
  let host := recordHost calls
  let program : Action UInt64 := do
    let _ ← loop 4 0 (fun _ _ => true) fun index state => do
      let _ ← writeStdoutSome (Bytes.build 1 (fun _ => index))
      if index == 1 then exit 4294967303 else pure (state + 1)
    let _ ← writeStderrSome bytes![99]
    pure 42
  match ← program.run host with
  | .exited code => check (code == 7) "exit did not preserve the low 32 bits"
  | _ => throw (IO.userError "expected exit from loop")
  check ((← calls.get) == #[.write 1 [0], .write 1 [1], .exit 7])
    "execution continued after exit"
  calls.set #[]
  let rejected := { host with
    exit := fun code => do
      calls.modify (·.push (.exit code))
      pure (.error "exit rejected") }
  trapped "exit rejected" (← program.run rejected)
  check ((← calls.get) == #[.write 1 [0], .write 1 [1], .exit 7])
    "execution continued after rejected exit"
  calls.set #[]
  let stopped := { host with
    write := fun output bytes => do
      calls.modify (·.push (.write output.fd bytes.data.data.toList))
      pure (.trapped "write stopped" 0) }
  trapped "write stopped" (← program.run stopped)
  check ((← calls.get) == #[.write 1 [0]]) "execution continued after host trap"
  calls.set #[]
  let failure := IO.userError "native stream failure"
  let throwing := { host with
    write := fun output bytes => do
      calls.modify (·.push (.write output.fd bytes.data.data.toList))
      throw failure }
  let caught ← try
    let _ ← program.run throwing
    pure false
  catch error => pure (error.toString == failure.toString)
  check caught "native IO.Error was converted or suppressed"
  check ((← calls.get) == #[.write 1 [0]]) "execution continued after IO.Error"

private def streams : IO Unit := do
  let input ← IO.mkRef ({ data := (bytes![0, 255, 65]).data } : IO.FS.Stream.Buffer)
  let output ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let error ← IO.mkRef ({} : IO.FS.Stream.Buffer)
  let host := NativeHost.ofStreams (IO.FS.Stream.ofBuffer input)
    (IO.FS.Stream.ofBuffer output) (IO.FS.Stream.ofBuffer error)
  let program : Action (UInt64 × UInt64 × UInt64 × UInt64) := do
    let zero ← readSome 0
    let data ← readSome 3
    let written ← writeStdoutSome data.bytes
    let _ ← writeStdoutSome Bytes.empty
    let diagnostic ← writeStderrSome bytes![128, 0]
    let eof ← readSome 3
    pure (zero.bytes.size, written.count, diagnostic.count, eof.bytes.size)
  returned (0, 3, 2, 0) (← program.run host)
  check ((← output.get).data.data.toList == [0, 255, 65]) "stdout binary bytes"
  check ((← error.get).data.data.toList == [128, 0]) "stderr binary bytes"
  let zeroCalls ← IO.mkRef ((0, 0) : UInt64 × UInt64)
  let stream := { IO.FS.Stream.ofBuffer output with
    write := fun _ => zeroCalls.modify fun (writes, flushes) => (writes + 1, flushes)
    flush := zeroCalls.modify fun (writes, flushes) => (writes, flushes + 1) }
  let emptyWrite : Action WriteResult := writeStdoutSome Bytes.empty
  match ← emptyWrite.run (NativeHost.ofStreams (IO.FS.Stream.ofBuffer input) stream stream) with
  | .returned result => check (result.errno == 0 && result.count == 0) "empty write result"
  | _ => throw (IO.userError "empty stream write did not return")
  check ((← zeroCalls.get) == (1, 1)) "empty write skipped the stream or flush"
  let failure := IO.userError "flush failed after writing"
  let failingStream := { IO.FS.Stream.ofBuffer output with flush := throw failure }
  let interrupted : Action Unit := do
    let _ ← writeStdoutSome bytes![17]
    let _ ← writeStderrSome bytes![99]
    pure ()
  let caught ← try
    let _ ← interrupted.run (NativeHost.ofStreams (IO.FS.Stream.ofBuffer input)
      failingStream (IO.FS.Stream.ofBuffer error))
    pure false
  catch exception => pure (exception.toString == failure.toString)
  check caught "stream flush IO.Error was converted or suppressed"
  check ((← output.get).data.data.toList == [0, 255, 65, 17]) "lost output before flush failure"
  check ((← error.get).data.data.toList == [128, 0]) "execution continued after flush failure"

/-- Flat calls through `NativeHost.withSys`: the argument calls report the given arguments,
the clocks follow Wasmtime's errnos, clock ids outside the enum give errno 28 and oversized
capacities errno 61 without a call while the largest accepted capacity reaches the host, replies of
the wrong shape raise an `IO.Error`, and a trap ends the action. -/
private def flatCalls : IO Unit := do
  let calls ← IO.mkRef #[]
  let host := (recordHost calls).withSys ["prog", "a b", ""]
  let program : Action (ArgsSizes × ArgsResult) := do
    let sizes ← argsSizesGet
    let arguments ← args
    pure (sizes, arguments)
  match ← program.run host with
  | .returned (sizes, arguments) =>
    check (sizes.errno == 0 && sizes.count == 3 && sizes.size == 10) "args_sizes_get reply"
    check (arguments.errno == 0 && arguments.count == 3 && arguments.size == 10 &&
      arguments.bytes.data.data.toList == "prog".toUTF8.data.toList ++ [0] ++
        "a b".toUTF8.data.toList ++ [0, 0]) "args reply"
  | _ => throw (IO.userError "argument calls did not return")
  let clocks : Action (List UInt64) := do
    let wall ← clockTimeGet 0 1
    let first ← clockTimeGet 1 1
    let second ← clockTimeGet 1 1
    let cpu ← clockTimeGet 2 1
    let thread ← clockTimeGet 3 1
    let other ← clockTimeGet 4 1
    let wide ← clockTimeGet 4294967296 1
    pure [wall.errno, first.errno, if first.time ≤ second.time then 0 else 1, cpu.errno, cpu.time,
      thread.errno, other.errno, wide.errno, wide.time,
      if 1700000000000000000 ≤ wall.time then 0 else 1]
  returned [0, 0, 0, 8, 0, 8, 28, 28, 0, 0] (← clocks.run host)
  let random : Action (List UInt64) := do
    let filled ← randomGet 16
    let zero ← randomGet 0
    let wide ← randomGet 4294967296
    pure [filled.errno, filled.bytes.size, zero.errno, zero.bytes.size, wide.errno, wide.bytes.size]
  returned [0, 16, 0, 0, 61, 0] (← random.run host)
  let capacityMessage := fun (call : LeanExe.Wasi.Call) (args : List LeanExe.Wasi.Arg) =>
    s!"{call.name} {(args.head?.map Arg.capacity).getD 0}"
  let reached : NativeHost :=
    { host with sys := fun call args => pure (.trapped (capacityMessage call args) []) }
  trapped "random_get 4294967295" (← (randomGet 4294967295).run reached)
  let empty := (recordHost calls).withSys []
  match ← args.run empty with
  | .returned arguments =>
    check (arguments.errno == 0 && arguments.count == 0 && arguments.bytes.size == 0) "empty args"
  | _ => throw (IO.userError "empty argument calls did not return")
  let wrongShape := { host with sys := fun _ _ => pure (.returned 0 [Bytes.empty]) }
  let caught ← try
    let _ ← (clockTimeGet 0 1).run wrongShape
    pure false
  catch error => pure (error.toString == "WASI native host returned an invalid clock_time_get reply")
  check caught "a reply of the wrong size was accepted"
  let stopped := { host with sys := fun _ _ => pure (.trapped "clock stopped" [bytes![0, 0, 0, 0, 0, 0, 0, 0]]) }
  trapped "clock stopped" (← (do let _ ← clockTimeGet 0 1; writeStdoutSome bytes![1]).run stopped)
  trapped "wasi clock_time_get: the native host does not serve it"
    (← (clockTimeGet 0 1).run (recordHost calls))
  check ((← calls.get).isEmpty) "a flat call reached the stream host"

def main : IO Unit := do
  primitives
  loops
  terminals
  streams
  flatCalls
  IO.println "native Action interpreter tests passed"

end NativeInterpreterTest

def main : IO Unit := NativeInterpreterTest.main
