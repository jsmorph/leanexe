import Verified.Wasi.ScriptHostMemory

namespace Verified.Wasi.ScriptHost

open Wasm LeanExe.Wasi

def replyCount (reply : Transfer α) (count : UInt32) : UInt32 :=
  match reply with
  | .returned errno _ => if errno = 0 then count else 4294967295
  | .trapped _ _ => 4294967295

def readAfter (before : Store (Observed World)) (pointer capacity count : UInt32) :
    Store (Observed World) :=
  let transition := readStep before.host.world capacity.toUInt64
  { before with
    mem := (before.mem.writeBytes pointer.toNat
      (readData before.host.world capacity.toUInt64)).write32 8 count
    host := {
      world := transition.2
      events := before.host.events ++ [.read capacity.toUInt64 transition.1] } }

def readInvoke (before : Store (Observed World)) (args : List Value) : HostResult (Observed World) :=
  match args with
  | [.i32 0, .i32 0, .i32 1, .i32 8] =>
      let pointer := before.mem.read32 0
      let capacity := before.mem.read32 4
      if 16 ≤ before.mem.pages * 65536 ∧
          pointer.toNat + capacity.toNat ≤ before.mem.pages * 65536 ∧
          pointer.toNat + capacity.toNat ≤ 2 ^ 32 ∧
          (capacity = 0 ∨ 16 ≤ pointer.toNat) then
        let transition := readStep before.host.world capacity.toUInt64
        let count := UInt32.ofNat (readData before.host.world capacity.toUInt64).length
        let after := readAfter before pointer capacity (replyCount transition.1 count)
        match transition.1 with
        | .returned errno _ => .Return [.i32 errno.toUInt32] after
        | .trapped message _ => .Trap after message
      else .Trap before "script: fd_read memory range is invalid"
  | _ => .Trap before "script: fd_read arguments are invalid"

def writeAfter (before : Store (Observed World)) (output : Output)
    (bytes : LeanExe.Bytes) (count : UInt32) : Store (Observed World) :=
  let transition := writeStep before.host.world output bytes
  { before with
    mem := before.mem.write32 8 count
    host := {
      world := transition.2
      events := before.host.events ++ [.write output bytes transition.1] } }

def writeOutput (before : Store (Observed World)) (output : Output) : HostResult (Observed World) :=
  let pointer := before.mem.read32 0
  let length := before.mem.read32 4
  if 16 ≤ before.mem.pages * 65536 ∧
      pointer.toNat + length.toNat ≤ before.mem.pages * 65536 ∧
      pointer.toNat + length.toNat ≤ 2 ^ 32 then
    let bytes := bytesOfList (before.mem.readBytes pointer.toNat length.toNat)
    let transition := writeStep before.host.world output bytes
    let after := writeAfter before output bytes
      (replyCount transition.1 transition.1.committed.toUInt32)
    match transition.1 with
    | .returned errno _ => .Return [.i32 errno.toUInt32] after
    | .trapped message _ => .Trap after message
  else .Trap before "script: fd_write memory range is invalid"

def writeInvoke (before : Store (Observed World)) (args : List Value) : HostResult (Observed World) :=
  match args with
  | [.i32 1, .i32 0, .i32 1, .i32 8] => writeOutput before .stdout
  | [.i32 2, .i32 0, .i32 1, .i32 8] => writeOutput before .stderr
  | _ => .Trap before "script: fd_write arguments are invalid"

def exitInvoke (before : Store (Observed World)) (args : List Value) : HostResult (Observed World) :=
  match args with
  | [.i32 code] =>
      match exitStep before.host.world code.toUInt64 with
      | (none, world) => .Trap
          { before with host := { world, events := before.host.events ++ [.exit code.toUInt64] } }
          exitTrap
      | (some message, world) => .Trap
          { before with host :=
            { world, events := before.host.events ++ [.exitTrap code.toUInt64 message] } } message
  | _ => .Trap before "script: proc_exit arguments are invalid"

def readFn : HostFn (Observed World) where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke := readInvoke

def writeFn : HostFn (Observed World) where
  params := [.i32, .i32, .i32, .i32]
  results := [.i32]
  invoke := writeInvoke

def exitFn : HostFn (Observed World) where
  params := [.i32]
  results := []
  invoke := exitInvoke

end Verified.Wasi.ScriptHost
