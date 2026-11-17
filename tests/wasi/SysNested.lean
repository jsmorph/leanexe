import LeanExe.Wasi.SysCalls
import LeanExe.Wasi.Interpreter
import Verified.Examples.WasiSysNested

/-! Native runs of the typed functions of `fd_read`, `fd_pread`, `fd_write`, `fd_pwrite`, and
`poll_oneoff` through a scripted host.  The host replies to each call with an errno and the outputs
that the script gives, recording each call's name and arguments.  A read returns the prefix of the
buffer of the count that the host returns, all of the buffer when the count exceeds the capacity,
and a poll returns the count and the fields of the first event at their witx offsets and widths,
written below as constants.  An argument that does not fit its field gives errno 61 without a call,
a reply with an errno leaves every result 0 or empty, and an event array one byte short raises an
`IO.Error`.  The `main` of `Verified.Examples.WasiSysNested`, run against a host whose `fd_close`
returns errno 8, returns the status 8, and 5 when `fd_write` in the bracket's body also returns
errno 5, so that the body's errno precedes the close's; neither run removes the file. -/

open LeanExe LeanExe.Wasi

namespace SysNestedTest

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- The bytes `1, 2, …, size`. -/
private def counting (size : Nat) : Bytes :=
  ⟨⟨((List.range size).map fun index => (index + 1).toUInt8).toArray⟩⟩

/-- The four little-endian bytes of `value`. -/
private def word32 (value : Nat) : Bytes :=
  ⟨⟨((List.range 4).map fun index => (value / 256 ^ index).toUInt8).toArray⟩⟩

/-- A host whose flat calls reply with `errno` and `outputs`, recording each call's name and
arguments. -/
private def scripted (calls : IO.Ref (Array (String × List Arg))) (errno : UInt64)
    (outputs : List Bytes) : NativeHost where
  read _ := pure (.returned 0 Bytes.empty)
  write _ bytes := pure (.returned 0 bytes.size)
  exit _ := pure (.ok ())
  sys call args := do
    calls.modify (·.push (call.name, args))
    pure (.returned errno outputs)

/-- A host that gives `path_open` descriptor 7 and answers `fd_close` with errno 8, the call named
`failing` with errno 5, and every other call with errno 0, each with zero outputs of the sizes
that the call requires, recording each call's name. -/
private def failingClose (calls : IO.Ref (Array String)) (failing : String) : NativeHost where
  read _ := pure (.returned 0 Bytes.empty)
  write _ bytes := pure (.returned 0 bytes.size)
  exit _ := pure (.ok ())
  sys call args := do
    calls.modify (·.push call.name)
    let errno : UInt64 :=
      if call.name == "fd_close" then 8 else if call.name == failing then 5 else 0
    let outputs : List Bytes :=
      (call.outputSizes [] args).map fun size => ⟨⟨Array.replicate size 0⟩⟩
    if call.name == "path_open" then pure (.returned 0 [bytes![7, 0, 0, 0]])
    else pure (.returned errno outputs)

private def result {α : Type} (action : Action α) (host : NativeHost) : IO α := do
  match ← action.run host with
  | .returned value => pure value
  | _ => throw (IO.userError "expected a return")

private def bytesOf (result : BytesResult) : UInt64 × List UInt8 :=
  (result.errno, result.bytes.data.toList)

private def wordOf (result : WordResult) : List UInt64 := [result.errno, result.value]

private def pollOf (result : PollResult) : List UInt64 :=
  [result.errno, result.count, result.userdata, result.error, result.type, result.nbytes,
    result.flags]

/-- The fields of an event whose byte `i` is `i + 1`: the userdata at 0, the error at 8 (two
bytes), the type at 10 (one byte), and the `nbytes` at 16 and the flags at 24 (two bytes) of its
`fd_readwrite`. -/
private def eventFields : List UInt64 :=
  [0x0807060504030201, 0x0a09, 0x0b, 0x1817161514131211, 0x1a19]

private def describe : Arg → String
  | .word value => s!"word {value}"
  | .bytes value => s!"bytes {value.data.toList}"
  | .space capacity => s!"space {capacity}"

/-- The name and the described arguments of the last recorded call. -/
private def last (calls : IO.Ref (Array (String × List Arg))) : IO (List String) := do
  match (← calls.get).back? with
  | some (name, args) => pure (name :: args.map describe)
  | none => throw (IO.userError "no call recorded")

private def checkCall (calls : IO.Ref (Array (String × List Arg))) (expected : List String) :
    IO Unit := do
  let recorded ← last calls
  check (recorded == expected) s!"call {recorded}"

def main : IO Unit := do
  let calls ← IO.mkRef (#[] : Array (String × List Arg))
  let file : Handle := ⟨5⟩
  let read ← result (fdRead file 16) (scripted calls 0 [counting 16, word32 10])
  check (bytesOf read == (0, (counting 10).data.toList)) s!"fd_read {bytesOf read}"
  checkCall calls ["fd_read", "word 5", "space 16"]
  let clamped ← result (fdRead file 16) (scripted calls 0 [counting 16, word32 20])
  check (bytesOf clamped == (0, (counting 16).data.toList)) s!"fd_read clamped {bytesOf clamped}"
  let pread ← result (fdPread file 8 5) (scripted calls 0 [counting 8, word32 8])
  check (bytesOf pread == (0, (counting 8).data.toList)) s!"fd_pread {bytesOf pread}"
  checkCall calls ["fd_pread", "word 5", "space 8", "word 5"]
  let failed ← result (fdRead file 16) (scripted calls 8 [counting 16, word32 10])
  check (bytesOf failed == (8, [])) s!"fd_read after an errno {bytesOf failed}"
  let written ← result (fdWrite file bytes![104, 105, 10]) (scripted calls 0 [word32 3])
  check (wordOf written == [0, 3]) s!"fd_write {wordOf written}"
  checkCall calls ["fd_write", "word 5", "bytes [104, 105, 10]"]
  let pwritten ← result (fdPwrite file bytes![104, 105] 7) (scripted calls 0 [word32 2])
  check (wordOf pwritten == [0, 2]) s!"fd_pwrite {wordOf pwritten}"
  checkCall calls ["fd_pwrite", "word 5", "bytes [104, 105]", "word 7"]
  let clock ← result (pollClock 1 0 0 0) (scripted calls 0 [counting 32, word32 1])
  check (pollOf clock == [0, 1] ++ eventFields) s!"poll_oneoff clock {pollOf clock}"
  checkCall calls ["poll_oneoff", "word 1", "word 0", "word 0", "word 0"]
  let readable ← result (pollRead file 1 1000) (scripted calls 0 [counting 64, word32 2])
  check (pollOf readable == [0, 2] ++ eventFields) s!"poll_oneoff read {pollOf readable}"
  checkCall calls ["poll_oneoff", "word 5", "word 1", "word 1000"]
  let writable ← result (pollWrite file 1 1000) (scripted calls 0 [counting 64, word32 1])
  check (pollOf writable == [0, 1] ++ eventFields) s!"poll_oneoff write {pollOf writable}"
  checkCall calls ["poll_oneoff", "word 5", "word 1", "word 1000"]
  let pollFailed ← result (pollRead file 1 1000) (scripted calls 28 [counting 64, word32 2])
  check (pollOf pollFailed == [28, 0, 0, 0, 0, 0, 0]) s!"poll after an errno {pollOf pollFailed}"
  let made := (← calls.get).size
  let capacity ← result (fdRead file 4294967296) (scripted calls 0 [])
  check (bytesOf capacity == (61, [])) s!"fd_read of capacity 2^32 {bytesOf capacity}"
  let clockId ← result (pollClock 4294967296 0 0 0) (scripted calls 0 [])
  check (pollOf clockId == [61, 0, 0, 0, 0, 0, 0]) s!"pollClock of clock 2^32 {pollOf clockId}"
  let flags ← result (pollClock 1 0 0 65536) (scripted calls 0 [])
  check (pollOf flags == [61, 0, 0, 0, 0, 0, 0]) s!"pollClock of flags 2^16 {pollOf flags}"
  let descriptor ← result (pollRead ⟨4294967296⟩ 1 1000) (scripted calls 0 [])
  check (pollOf descriptor == [61, 0, 0, 0, 0, 0, 0]) s!"pollRead of 2^32 {pollOf descriptor}"
  check ((← calls.get).size == made) "a rejected argument reached the host"
  let shortCaught ← try
    let _ ← (pollRead file 1 1000).run (scripted calls 0 [counting 63, word32 2])
    pure false
  catch _ => pure true
  check shortCaught "an event array one byte short was accepted"
  for (failing, expected) in ([("", 8), ("fd_write", 5)] : List (String × UInt64)) do
    let exampleCalls ← IO.mkRef (#[] : Array String)
    let status ← result Verified.Examples.WasiSysNested.main (failingClose exampleCalls failing)
    let made ← exampleCalls.get
    check (status == expected && made.back? == some "fd_close" &&
        !made.contains "path_unlink_file")
      s!"the example after a failed close and {failing}: status {status}, calls {made}"
  IO.println "nested call native cases passed: 17"

end SysNestedTest

def main : IO Unit := SysNestedTest.main
