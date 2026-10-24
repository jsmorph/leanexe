import Verified.Wasi.ScriptHostContracts
import Verified.Examples.WasiCodegen

open Wasm LeanExe.Wasi Verified.Wasi Verified.Wasi.ScriptHost

namespace ScriptHostTest

private instance : Inhabited (Observed World) := ⟨{ world := {}, events := [] }⟩

private def equal [BEq α] [Repr α] (label : String) (actual expected : α) : IO Unit :=
  unless actual == expected do
    throw (IO.userError s!"{label}: expected {repr expected}, observed {repr actual}")

private inductive EventView where
  | read (capacity : UInt64) (errno : Option UInt64) (bytes : List UInt8) (message : String)
  | write (fd : UInt64) (bytes : List UInt8) (errno : Option UInt64) (count : UInt64) (message : String)
  | exit (code : UInt64)
  | exitTrap (code : UInt64) (message : String)
  deriving BEq, Repr

private def eventView : Event → EventView
  | .read capacity (.returned errno bytes) => .read capacity (some errno) bytes.data.data.toList ""
  | .read capacity (.trapped message bytes) => .read capacity none bytes.data.data.toList message
  | .write output bytes (.returned errno count) =>
      .write output.fd bytes.data.data.toList (some errno) count ""
  | .write output bytes (.trapped message count) =>
      .write output.fd bytes.data.data.toList none count message
  | .exit code => .exit code
  | .exitTrap code message => .exitTrap code message

private def checkEvents (store : Store (Observed World)) (expected : List EventView) : IO Unit :=
  equal "ordered events" (store.host.events.map eventView) expected

private def initial (target : Wasm.Module) (script : List Request)
    (input : List UInt8 := []) (links : Links := {}) : Store (Observed World) :=
  { (target.initialStore : Store (Observed World)) with host := {
      world := { queues := { first := input }, links, script }
      events := [] } }

private def invoke (target : Wasm.Module) (name : String) (arguments : List UInt64)
    (store : Store (Observed World)) : IO (Continuation (Observed World)) := do
  let some entry := target.findExport name
    | throw (IO.userError s!"missing export {name}")
  return exec 512 target store { values := (arguments.map Value.i64).reverse }
    [.call entry] (env target)

private def scalar (expected : UInt64) : Continuation (Observed World) → IO (Store (Observed World))
  | .Fallthrough store locals => do
      match locals.values with
      | [.i64 value] => equal "return value" value expected
      | _ => throw (IO.userError "scalar call returned an unexpected stack")
      return store
  | .Trap _ message => throw (IO.userError s!"scalar call trapped: {message}")
  | .Invalid message => throw (IO.userError s!"scalar call was invalid: {message}")
  | .OutOfFuel => throw (IO.userError "scalar call exhausted its fuel")
  | _ => throw (IO.userError "scalar call produced an unexpected continuation")

private def trapped (expected : String) : Continuation (Observed World) → IO (Store (Observed World))
  | .Trap store message => do
      equal "terminal message" message expected
      return store
  | .OutOfFuel => throw (IO.userError "terminal call exhausted its fuel")
  | _ => throw (IO.userError "terminal call produced an unexpected continuation")

private def counter (target : Wasm.Module) (store : Store (Observed World)) (name : String) : IO UInt64 := do
  let some (_, index) := target.globalExports.find? (fun entry => entry.1 == name)
    | throw (IO.userError s!"missing counter {name}")
  let some (.i64 value) := store.globals.globals[index]?
    | throw (IO.userError s!"invalid counter {name}")
  return value

private def stats (store : Store (Observed World)) (allocations releases : UInt64) : IO Unit := do
  equal "allocation count" (← counter Verified.Examples.WasiCodegen.callable store "allocCount") allocations
  equal "release count" (← counter Verified.Examples.WasiCodegen.callable store "freeCount") releases

private def completed (store : Store (Observed World)) : IO Unit := do
  equal "remaining requests" store.host.world.script.length 0
  equal "exit marker" store.host.world.exited none

private def writeCase (policy : Policy) (errno count : UInt64) (committed : List UInt8) : IO Unit := do
  let target := Verified.Examples.WasiCodegen.callable
  let start := initial target [.write .stdout policy]
  let final ← scalar (if errno == 0 then count else 0) (← invoke target "writeLiteral" [] start)
  equal "stdout queue" final.host.world.queues.second committed
  checkEvents final [.write 1 [65, 0, 255] (some errno) count ""]
  if errno != 0 then equal "poisoned error count" (final.mem.read32 8) (4294967295 : UInt32)
  stats final 1 1
  completed final

private def readCase (capacity : UInt64) (policy : Policy) (errno : UInt64)
    (committed offered output : List UInt8) (written : UInt64) (allocations : UInt64) : IO Unit := do
  let target := Verified.Examples.WasiCodegen.callable
  let start := initial target [.read policy, .write .stdout (.returned 0 (by decide) written)]
    [0, 255, 65, 128]
  let final ← scalar written (← invoke target "echo" [capacity] start)
  equal "remaining stdin" final.host.world.queues.first ([0, 255, 65, 128].drop committed.length)
  equal "stdout queue" final.host.world.queues.second output
  checkEvents final [.read capacity (some errno) committed "", .write 1 offered (some 0) written ""]
  stats final allocations allocations
  completed final

private def transferCases : IO Unit := do
  writeCase (.returned 0 (by decide) 1) 0 1 [65]
  writeCase (.returned 0 (by decide) 0) 0 0 []
  writeCase (.returned 29 (by decide) 2) 29 2 [65, 0]
  readCase 4 (.returned 0 (by decide) 2) 0 [0, 255] [0, 255] [0] 1 1
  readCase 4 (.returned 0 (by decide) 0) 0 [] [] [] 0 1
  readCase 4 (.returned 29 (by decide) 2) 29 [0, 255] [] [] 0 1
  readCase 0 (.returned 27 (by decide) 0) 27 [] [] [] 0 0
  let target := Verified.Examples.WasiCodegen.callable
  let discarded ← scalar 7 (← invoke target "discardRead" [4]
    (initial target [.read (.returned 29 (by decide) 2)] [0, 255, 65, 128]))
  equal "discarded error input" discarded.host.world.queues.first [65, 128]
  equal "poisoned read error count" (discarded.mem.read32 8) (4294967295 : UInt32)
  checkEvents discarded [.read 4 (some 29) [0, 255] ""]
  stats discarded 1 1
  completed discarded

private def trapCases : IO Unit := do
  let target := Verified.Examples.WasiCodegen.callable
  let writeTrap ← trapped "write stopped" (← invoke target "writeLiteral" []
    (initial target [.write .stdout (.trapped "write stopped" 2)]))
  equal "output committed before trap" writeTrap.host.world.queues.second [65, 0]
  checkEvents writeTrap [.write 1 [65, 0, 255] none 2 "write stopped"]
  stats writeTrap 1 0
  completed writeTrap
  let readTrap ← trapped "read stopped" (← invoke target "echo" [4]
    (initial target [.read (.trapped "read stopped" 2),
      .write .stdout (.returned 0 (by decide) 4)] [0, 255, 65, 128]))
  equal "input consumed before trap" readTrap.host.world.queues.first [65, 128]
  equal "queued write after read trap" readTrap.host.world.script.length 1
  equal "stdout after read trap" readTrap.host.world.queues.second []
  checkEvents readTrap [.read 4 none [0, 255] "read stopped"]
  stats readTrap 1 0
  let loopTrap ← trapped "loop stopped" (← invoke target "wordLoop" [3]
    (initial target [.write .stdout (.returned 0 (by decide) 1),
      .write .stdout (.trapped "loop stopped" 1), .write .stdout (.returned 0 (by decide) 1)]))
  equal "loop output before trap" loopTrap.host.world.queues.second [46, 46]
  equal "queued loop step" loopTrap.host.world.script.length 1
  checkEvents loopTrap [.write 1 [46] (some 0) 1 "", .write 1 [46] none 1 "loop stopped"]
  stats loopTrap 2 1

private def aliasCases : IO Unit := do
  let target := Verified.Examples.WasiCodegen.callable
  let start := initial target [.write .stdout (.returned 0 (by decide) 1),
    .write .stderr (.returned 0 (by decide) 1)] [] { stdout := .second, stderr := .second }
  let first ← scalar 1 (← invoke target "branch" [1] start)
  let final ← scalar 1 (← invoke target "branch" [0] first)
  equal "shared output queue" final.host.world.queues.second [89, 78]
  checkEvents final [.write 1 [89] (some 0) 1 "", .write 2 [78] (some 0) 1 ""]
  stats final 2 2
  completed final
  let inputAlias := initial target [.read (.returned 0 (by decide) 1),
    .write .stdout (.returned 0 (by decide) 1), .read (.returned 0 (by decide) 3),
    .write .stdout (.returned 0 (by decide) 3)] [65, 66, 67] { stdout := .first }
  let first ← scalar 1 (← invoke target "echo" [2] inputAlias)
  let final ← scalar 3 (← invoke target "echo" [3] first)
  equal "shared input/output queue" final.host.world.queues.first [66, 67, 65]
  checkEvents final [.read 2 (some 0) [65] "", .write 1 [65] (some 0) 1 "",
    .read 3 (some 0) [66, 67, 65] "", .write 1 [66, 67, 65] (some 0) 3 ""]
  stats final 2 2
  completed final

private def exitCases : IO Unit := do
  let target := Verified.Examples.WasiCodegen.callable
  let accepted ← trapped exitTrap (← invoke target "exitCode" [18446744073709551615]
    (initial target [.write .stdout (.returned 0 (by decide) 1), .exit .accepted,
      .write .stderr (.returned 0 (by decide) 1)]))
  equal "raw accepted exit status" accepted.host.world.exited (some 4294967295)
  equal "queued write after exit" accepted.host.world.script.length 1
  equal "stdout before exit" accepted.host.world.queues.second [88]
  checkEvents accepted [.write 1 [88] (some 0) 1 "", .exit 4294967295]
  stats accepted 1 1
  let command := Verified.Examples.WasiCodegen.exitedCommand
  let rejected ← trapped "exit refused" (← invoke command "_start" []
    (initial command [.write .stdout (.returned 0 (by decide) 1), .exit (.rejected "exit refused"),
      .write .stderr (.returned 0 (by decide) 1)]))
  equal "rejected exit marker" rejected.host.world.exited none
  equal "queued write after rejection" rejected.host.world.script.length 1
  equal "stderr after rejected exit" rejected.host.world.queues.third []
  checkEvents rejected [.write 1 [88] (some 0) 1 "", .exitTrap 7 "exit refused"]
  let accepted ← trapped exitTrap (← invoke command "_start" []
    (initial command [.write .stdout (.returned 0 (by decide) 1), .exit .accepted,
      .write .stderr (.returned 0 (by decide) 1)]))
  equal "explicit command exit" accepted.host.world.exited (some 7)
  equal "queued write after command exit" accepted.host.world.script.length 1
  equal "stderr after accepted exit" accepted.host.world.queues.third []
  checkEvents accepted [.write 1 [88] (some 0) 1 "", .exit 7]
  let command := Verified.Examples.WasiCodegen.returnedCommand
  let returned ← trapped exitTrap (← invoke command "_start" []
    (initial command [.write .stdout (.returned 0 (by decide) 3), .exit .accepted]))
  equal "returned command exit" returned.host.world.exited (some 3)
  equal "returned command output" returned.host.world.queues.second [65, 0, 255]
  checkEvents returned [.write 1 [65, 0, 255] (some 0) 3 "", .exit 3]

example : (env Verified.Examples.WasiCodegen.callable).Satisfies
    Verified.Examples.WasiCodegen.callable (hostSpec sourceHost) := env_satisfies _ rfl

def main : IO Unit := do
  transferCases
  trapCases
  aliasCases
  exitCases
  IO.println "Scripted Talos WASI tests passed: 17 cases"

end ScriptHostTest

def main : IO Unit := ScriptHostTest.main
