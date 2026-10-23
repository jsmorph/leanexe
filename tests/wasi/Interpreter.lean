import LeanExe.Wasi.Interpreter

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

def main : IO Unit := do
  primitives
  loops
  terminals
  streams
  IO.println "native Action interpreter tests passed"

end NativeInterpreterTest

def main : IO Unit := NativeInterpreterTest.main
