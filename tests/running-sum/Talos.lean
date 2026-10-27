import Demos.RunningSum.Module
import Verified.Wasi.ScriptHostContracts

open Wasm LeanExe.Wasi Verified.Wasi Verified.Wasi.ScriptHost

private instance : Inhabited (Observed World) := ⟨{ world := {}, events := [] }⟩

private def equal [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {repr expected}, observed {repr actual}")

private def check (input expected : String) (requests : List Request)
    (status : Option UInt64) (message : String := exitTrap) (remaining : Nat := 0) : IO Unit := do
  let target := Demos.RunningSum.module
  let initial : Store (Observed World) :=
    { (target.initialStore : Store (Observed World)) with host := {
        world := { queues := { first := input.toUTF8.data.toList }, script := requests }
        events := [] } }
  let some entry := target.findExport "_start"
    | throw (IO.userError "Missing running-sum entry")
  let result := exec 2048 target initial {} [.call entry] (env target)
  let .Trap final cause := result
    | throw (IO.userError "Running sum did not reach a terminal outcome")
  equal "terminal message" cause message
  equal "stdout" final.host.world.queues.second expected.toUTF8.data.toList
  equal "stderr" final.host.world.queues.third []
  equal "exit status" final.host.world.exited status
  equal "pending operations" final.host.world.script.length remaining
  let writes := final.host.events.filterMap fun event => match event with
    | .write _ bytes (.returned _ count) => some (bytes.data.extract 0 count.toNat)
    | .write _ bytes (.trapped _ count) => some (bytes.data.extract 0 count.toNat)
    | _ => none
  equal "committed write prefixes" (writes.foldl (· ++ ·) ByteArray.empty).data.toList
    expected.toUTF8.data.toList

private def read (count : UInt64) : Request := .read (.returned 0 (by decide) count)
private def write (count : UInt64) : Request := .write .stdout (.returned 0 (by decide) count)

def main : IO Unit := do
  check "12\n-5\n20" "12\n7\n27\n"
    [read 2, read 1, write 0, write 1, write 2, read 3, write 2,
      read 2, read 0, write 3, .exit .accepted] (some 0)
  check "1\n2\n" "1\n"
    [read 2, write 2, .read (.returned 29 (by decide) 1), .exit .accepted] (some 29)
  check "12\n" "1"
    [read 3, .write .stdout (.returned 29 (by decide) 1), .exit .accepted] (some 29)
  check "12\n" "1"
    [read 3, .write .stdout (.trapped "write stopped" 1), write 2]
    none "write stopped" 1
  check "12\n" "12\n"
    [read 3, write 3, read 0, .exit (.rejected "exit refused")]
    none "exit refused"
  check "1\n2x\n3\n" "1\n" [read 8, write 2, .exit .accepted] (some 28)
  IO.println "Running sum scripted Wasm: 6 cases passed"
