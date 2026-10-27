import Verified.Wasi.PureInstructionsBasic

namespace Verified.Wasi.PureTransport

open Wasm

theorem load8_step {State : Type} (fuel : Nat) (m : Module) (store : Store State)
    (s : Locals) (off : UInt32) (host : HostEnv State) :
    execOne (fuel + 1) m store s (.load8U off) host =
      match s.values with
      | .i32 address :: rest =>
        if address.toNat + off.toNat + 1 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough store
          { s with values := .i32 (store.mem.read8 (address + off)).toUInt32 :: rest }
      | .i64 address :: rest =>
        if address.toNat + off.toNat + 1 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough store
          { s with values := .i32 (store.mem.read8 (address.toUInt32 + off)).toUInt32 :: rest }
      | _ => .Invalid "load8U: ill-shaped operand stack" := by
  rw [execOne.eq_def]
  rfl

theorem load32_step {State : Type} (fuel : Nat) (m : Module) (store : Store State)
    (s : Locals) (off : UInt32) (host : HostEnv State) :
    execOne (fuel + 1) m store s (.load32 off) host =
      match s.values with
      | .i32 address :: rest =>
        if address.toNat + off.toNat + 4 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough store
          { s with values := .i32 (store.mem.read32 (address + off)) :: rest }
      | .i64 address :: rest =>
        if address.toNat + off.toNat + 4 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough store
          { s with values := .i32 (store.mem.read32 (address.toUInt32 + off)) :: rest }
      | _ => .Invalid "load32: ill-shaped operand stack" := by
  rw [execOne.eq_def]
  rfl

theorem load64_step {State : Type} (fuel : Nat) (m : Module) (store : Store State)
    (s : Locals) (off : UInt32) (host : HostEnv State) :
    execOne (fuel + 1) m store s (.load64 off) host =
      match s.values with
      | .i32 address :: rest =>
        if address.toNat + off.toNat + 8 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough store
          { s with values := .i64 (store.mem.read64 (address + off)) :: rest }
      | .i64 address :: rest =>
        if address.toNat + off.toNat + 8 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough store
          { s with values := .i64 (store.mem.read64 (address.toUInt32 + off)) :: rest }
      | _ => .Invalid "load64: ill-shaped operand stack" := by
  rw [execOne.eq_def]
  rfl

theorem store8_step {State : Type} (fuel : Nat) (m : Module) (store : Store State)
    (s : Locals) (off : UInt32) (host : HostEnv State) :
    execOne (fuel + 1) m store s (.store8 off) host =
      match s.values with
      | .i32 value :: .i32 address :: rest =>
        if address.toNat + off.toNat + 1 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough { store with mem := store.mem.write8 (address + off) value.toUInt8 }
          { s with values := rest }
      | .i32 value :: .i64 address :: rest =>
        if address.toNat + off.toNat + 1 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough
          { store with mem := store.mem.write8 (address.toUInt32 + off) value.toUInt8 }
          { s with values := rest }
      | _ => .Invalid "store8: ill-shaped operand stack" := by
  rw [execOne.eq_def]
  rfl

theorem store32_step {State : Type} (fuel : Nat) (m : Module) (store : Store State)
    (s : Locals) (off : UInt32) (host : HostEnv State) :
    execOne (fuel + 1) m store s (.store32 off) host =
      match s.values with
      | .i32 value :: .i32 address :: rest =>
        if address.toNat + off.toNat + 4 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough { store with mem := store.mem.write32 (address + off) value }
          { s with values := rest }
      | .i32 value :: .i64 address :: rest =>
        if address.toNat + off.toNat + 4 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough { store with mem := store.mem.write32 (address.toUInt32 + off) value }
          { s with values := rest }
      | _ => .Invalid "store32: ill-shaped operand stack" := by
  rw [execOne.eq_def]
  rfl

theorem store64_step {State : Type} (fuel : Nat) (m : Module) (store : Store State)
    (s : Locals) (off : UInt32) (host : HostEnv State) :
    execOne (fuel + 1) m store s (.store64 off) host =
      match s.values with
      | .i64 value :: .i32 address :: rest =>
        if address.toNat + off.toNat + 8 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough { store with mem := store.mem.write64 (address + off) value }
          { s with values := rest }
      | .i64 value :: .i64 address :: rest =>
        if address.toNat + off.toNat + 8 > store.mem.pages * 65536 then
          .Trap store "out of bounds memory access"
        else .Fallthrough { store with mem := store.mem.write64 (address.toUInt32 + off) value }
          { s with values := rest }
      | _ => .Invalid "store64: ill-shaped operand stack" := by
  rw [execOne.eq_def]
  rfl

end Verified.Wasi.PureTransport
