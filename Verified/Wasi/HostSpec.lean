import Verified.Wasi.ABI
import Verified.Wasi.Observed
import Verified.Bytes.Memory
import Interpreter.Wasm.Host.Registry

namespace Verified.Wasi

open Wasm LeanExe LeanExe.Wasi

def InRange (address : Nat) (region : Nat × Nat) : Prop :=
  region.1 ≤ address ∧ address < region.1 + region.2

structure GuestFrame (before after : Store World) (writable : List (Nat × Nat)) : Prop where
  resources : after.mapHost (fun _ => ()) =
    { before.mapHost (fun _ => ()) with mem := after.mem }
  pages : after.mem.pages = before.mem.pages
  bytes : ∀ address, (∀ region ∈ writable, ¬InRange address region) →
    after.mem.bytes address = before.mem.bytes address

theorem GuestFrame.globals {before after : Store World} {writable : List (Nat × Nat)}
    (h : GuestFrame before after writable) : after.globals = before.globals := by
  exact congrArg (fun store : Store Unit => store.globals) h.resources

theorem GuestFrame.memoryCaps {before after : Store World} {writable : List (Nat × Nat)}
    (h : GuestFrame before after writable) : after.memoryCaps = before.memoryCaps := by
  exact congrArg (fun store : Store Unit => store.memoryCaps) h.resources

structure WriteRequest (before : Store World) (args : List Value) (output : Output)
    (pointer : UInt32) (bytes : LeanExe.Bytes) : Prop where
  arguments : args = [.i32 output.fd.toUInt32, .i32 0, .i32 1, .i32 8]
  scratch : 16 ≤ before.mem.pages * 65536
  pointer_eq : before.mem.read32 0 = pointer
  length_eq : before.mem.read32 4 = UInt32.ofNat bytes.data.size
  size : bytes.data.size < 2 ^ 32
  data : Bytes.At before.mem pointer.toUInt64 bytes

structure ReadRequest (before : Store World) (args : List Value)
    (pointer capacity : UInt32) : Prop where
  arguments : args = [.i32 0, .i32 0, .i32 1, .i32 8]
  scratch : 16 ≤ before.mem.pages * 65536
  pointer_eq : before.mem.read32 0 = pointer
  length_eq : before.mem.read32 4 = capacity
  memory : pointer.toNat + capacity.toNat ≤ before.mem.pages * 65536
  address : pointer.toNat + capacity.toNat ≤ 2 ^ 32
  separate : capacity = 0 ∨ 16 ≤ pointer.toNat

def writeContract (host : Host World) : HostContract (Observed World) :=
  fun before args result => ∀ output pointer bytes,
    WriteRequest before args output pointer bytes →
    match result with
    | .Return values after => ∃ (errno committed : UInt64),
        values = [.i32 errno.toUInt32] ∧
        (observedHost host).write before.host output bytes (.returned errno committed) after.host ∧
        GuestFrame before after [ABI.scratch] ∧
        (errno = 0 → after.mem.read32 8 = committed.toUInt32)
    | .Trap after message => ∃ committed : UInt64,
        (observedHost host).write before.host output bytes (.trapped message committed) after.host ∧
        GuestFrame before after [ABI.scratch]
    | .Throw _ _ _ => False

def readContract (host : Host World) : HostContract (Observed World) :=
  fun before args result => ∀ pointer capacity,
    ReadRequest before args pointer capacity →
    match result with
    | .Return values after => ∃ (errno : UInt64) (committed : LeanExe.Bytes),
        values = [.i32 errno.toUInt32] ∧
        (observedHost host).read before.host capacity.toUInt64
          (.returned errno committed) after.host ∧
        GuestFrame before after [ABI.scratch, (pointer.toNat, capacity.toNat)] ∧
        (errno = 0 → Bytes.At after.mem pointer.toUInt64 committed ∧
          after.mem.read32 8 = UInt32.ofNat committed.data.size)
    | .Trap after message => ∃ committed : LeanExe.Bytes,
        (observedHost host).read before.host capacity.toUInt64
          (.trapped message committed) after.host ∧
        GuestFrame before after [ABI.scratch, (pointer.toNat, capacity.toNat)]
    | .Throw _ _ _ => False

def exitTrap : String := "wasi proc_exit"

def exitContract (host : Host World) : HostContract (Observed World) :=
  fun before args result => ∀ code : UInt32, args = [.i32 code] →
    match result with
    | .Trap after message => GuestFrame before after [] ∧
        ((message = exitTrap ∧ (observedHost host).exit before.host code.toUInt64 after.host) ∨
          (observedHost host).exitTrap before.host code.toUInt64 message after.host)
    | .Return _ _ | .Throw _ _ _ => False

def hostSpec (host : Host World) : HostSpec (Observed World) :=
  { contracts := [readContract host, writeContract host, exitContract host] }

theorem hostSpec_read (host : Host World) :
    (hostSpec host).contracts[0]? = some (readContract host) := rfl

theorem hostSpec_write (host : Host World) :
    (hostSpec host).contracts[1]? = some (writeContract host) := rfl

theorem hostSpec_exit (host : Host World) :
    (hostSpec host).contracts[2]? = some (exitContract host) := rfl

end Verified.Wasi
