import Demos.RunningSumFp.Module
import Verified.Wasi.ScriptHostContracts

open Wasm LeanExe.Wasi Verified.Wasi Verified.Wasi.ScriptHost

private instance : Inhabited (Observed World) := ⟨{ world := {}, events := [] }⟩

private def equal [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {repr expected}, observed {repr actual}")

private def check (input expected : String) (requests : List Request)
    (status : Option UInt64) (message : String := exitTrap) (remaining : Nat := 0) : IO Unit := do
  let target := Demos.RunningSumFp.module
  let initial : Store (Observed World) :=
    { (target.initialStore : Store (Observed World)) with host := {
        world := { queues := { first := input.toUTF8.data.toList }, script := requests }
        events := [] } }
  let some entry := target.findExport "_start"
    | throw (IO.userError "Missing running-sumfp entry")
  let result := exec 4096 target initial {} [.call entry] (env target)
  let .Trap final cause := result
    | throw (IO.userError "Running sumfp did not reach a terminal outcome")
  equal "terminal message" cause message
  equal "stdout" final.host.world.queues.second expected.toUTF8.data.toList
  equal "stderr" final.host.world.queues.third []
  equal "exit status" final.host.world.exited status
  equal "pending operations" final.host.world.script.length remaining
  let writes := final.host.events.filterMap fun event => match event with
    | .write .stdout bytes reply => some (bytes.data.extract 0 reply.committed.toNat)
    | _ => none
  equal "committed stdout prefixes" (writes.foldl (· ++ ·) ByteArray.empty).data.toList
    expected.toUTF8.data.toList

private def read (count : UInt64) : Request := .read (.returned 0 (by decide) count)
private def write (count : UInt64) : Request := .write .stdout (.returned 0 (by decide) count)
private def writeText (text : String) : Request := write text.toUTF8.size.toUInt64

private def cases : List (String × (Unit → IO Unit)) := [
  ("short-transfers", fun _ => check "-0\n0\n-0" "0e0\n0e0\n0e0\n"
    [read 1, read 2, write 0, write 1, write 1, write 2, read 2, write 1, write 3,
      read 2, read 0, write 2, write 2, .exit .accepted] (some 0)),
  ("read-error", fun _ => check "0\n0\n" "0e0\n"
    [read 2, writeText "0e0\n", .read (.returned 29 (by decide) 1), .exit .accepted] (some 29)),
  ("write-error", fun _ => check "-0\n" "0e"
    [read 3, .write .stdout (.returned 29 (by decide) 2), .exit .accepted] (some 29)),
  ("write-trap", fun _ => check "-0\n" "0e"
    [read 3, .write .stdout (.trapped "write stopped" 2), write 2]
    none "write stopped" 1),
  ("exit-rejection", fun _ => check "0\n" "0e0\n"
    [read 2, writeText "0e0\n", read 0, .exit (.rejected "exit refused")]
    none "exit refused"),
  ("invalid-line", fun _ => check "0\n2x\n3\n" "0e0\n"
    [read 7, writeText "0e0\n", .exit .accepted] (some 28)),
  ("underflow", fun _ => check "1e-400\n-1e-400\n" "0e0\n0e0\n"
    [read 15, writeText "0e0\n", writeText "0e0\n", read 0,
      .exit .accepted] (some 0)),
  ("infinities", fun _ => check "Infinity\n-Infinity\n1\n" "Infinity\nNaN\nNaN\n"
    [read 21, writeText "Infinity\n", writeText "NaN\n", writeText "NaN\n", read 0,
      .exit .accepted] (some 0))]

def main (arguments : List String) : IO Unit := do
  let selected ← match arguments with
    | [] => pure cases
    | [name] =>
        match cases.find? (fun test => test.1 == name) with
        | some test => pure [test]
        | none => throw (IO.userError s!"Unknown scripted case: {name}")
    | _ => throw (IO.userError "Usage: Talos.lean [CASE_NAME]")
  for (name, run) in selected do
    IO.println s!"Running sumfp scripted Wasm: {name}"
    (← IO.getStdout).flush
    run ()
    IO.println s!"Running sumfp scripted Wasm passed: {name}"
    (← IO.getStdout).flush
  IO.println s!"Running sumfp scripted Wasm: {selected.length} cases passed"
