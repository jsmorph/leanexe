import Project.Core.Invoke
import Init.Data.ByteArray.Lemmas

namespace Project.Core.ByteMemory

open Wasm

/-- The native array represents all accessible bytes of a bounded linear memory. -/
structure BytesAt (bytes : ByteArray) (memory : Mem) : Prop where
  size : bytes.size = memory.pages * 65536
  bounded : bytes.size ≤ 2 ^ 32
  byte : ∀ index, index < bytes.size → memory.bytes index = bytes[index]!

theorem address_toNat (address : UInt64) (bounded : address.toNat < 2 ^ 32) :
    address.toUInt32.toNat = address.toNat := by
  rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt bounded]

theorem BytesAt.read {bytes : ByteArray} {memory : Mem}
    (represented : BytesAt bytes memory) (address : UInt64)
    (valid : address.toNat < bytes.size) :
    memory.read8 address.toUInt32 = bytes[address.toNat]! := by
  have bounded : address.toNat < 2 ^ 32 := Nat.lt_of_lt_of_le valid represented.bounded
  simpa [Mem.read8, address_toNat address bounded] using represented.byte address.toNat valid

theorem BytesAt.access {bytes : ByteArray} {memory : Mem}
    (represented : BytesAt bytes memory) (address : UInt64)
    (valid : address.toNat < bytes.size) :
    address.toUInt32.toNat + 1 ≤ memory.pages * 65536 := by
  rw [address_toNat address (Nat.lt_of_lt_of_le valid represented.bounded), ← represented.size]
  omega

theorem BytesAt.write {bytes : ByteArray} {memory : Mem}
    (represented : BytesAt bytes memory) (address : UInt64) (value : UInt8)
    (valid : address.toNat < bytes.size) :
    BytesAt (bytes.set! address.toNat value) (memory.write8 address.toUInt32 value) := by
  have bounded : address.toNat < 2 ^ 32 := Nat.lt_of_lt_of_le valid represented.bounded
  refine ⟨by simpa [Mem.write8] using represented.size,
    by simpa using represented.bounded, ?_⟩
  intro index within
  have original : index < bytes.size := by simpa using within
  by_cases same : index = address.toNat
  · subst index
    simp [Mem.write8, address_toNat address bounded, valid]
  · rw [ByteArray.getElem!_set!_ne _ _ _ _ (Ne.symm same)]
    simpa [Mem.write8, address_toNat address bounded, same] using
      represented.byte index original

def readFunction : Wasm.Function :=
  { params := [.i64]
    body := [.localGet 0, .wrapI64, .load8U 0, .extendUI32]
    results := [.i64] }

def writeFunction : Wasm.Function :=
  { params := [.i64, .i64]
    body := [.localGet 0, .wrapI64, .localGet 1, .wrapI64, .store8 0, .constI64 0]
    results := [.i64] }

def readFrame (address value : UInt64) : Locals :=
  { params := [.i64 address], values := [.i64 value] }

def writeFrame (address value : UInt64) : Locals :=
  { params := [.i64 address, .i64 value], values := [.i64 0] }

def writeStore (initial : Store α) (address value : UInt64) : Store α :=
  { initial with mem := initial.mem.write8 address.toUInt32 value.toUInt8 }

/-- A byte store leaves every other store resource exactly unchanged. -/
theorem writeStore_resources (initial : Store α) (address value : UInt64) :
    { writeStore initial address value with mem := initial.mem } = initial := rfl

theorem writeStore_bytes {bytes : ByteArray} {initial : Store α}
    (represented : BytesAt bytes initial.mem) (address value : UInt64)
    (valid : address.toNat < bytes.size) :
    BytesAt (bytes.set! address.toNat value.toUInt8) (writeStore initial address value).mem :=
  represented.write address value.toUInt8 valid

private theorem wrap_eq (value : UInt64) :
    UInt32.ofNat (value.toNat % 4294967296) = value.toUInt32 := by
  apply UInt32.toNat.inj
  simp

private theorem wrap_byte (value : UInt64) :
    UInt8.ofNat (value.toNat % 4294967296) = value.toUInt8 := by
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat', UInt64.toNat_toUInt8, Nat.reducePow]
  omega

private theorem extend_byte (value : UInt8) :
    UInt64.ofNat value.toUInt32.toNat = value.toUInt64 := by
  apply UInt64.toNat.inj
  simp only [UInt64.toNat_ofNat', UInt8.toNat_toUInt32, UInt8.toNat_toUInt64]
  exact Nat.mod_eq_of_lt (Nat.lt_trans value.toNat_lt (by decide))

theorem read_body_wp (module_ : Wasm.Module) (host : HostEnv α) (initial : Store α)
    (bytes : ByteArray) (address : UInt64)
    (represented : BytesAt bytes initial.mem) (valid : address.toNat < bytes.size)
    (Q : Assertion α)
    (next : Q (.Fallthrough initial (readFrame address bytes[address.toNat]!.toUInt64))) :
    wp module_ readFunction.body Q initial (readFunction.toLocals [.i64 address]) host := by
  have bound : ¬initial.mem.pages * 65536 ≤ address.toNat % 4294967296 := by
    have := represented.size
    omega
  have read := represented.read address valid
  simpa [readFunction, Function.toLocals, Locals.get, wrap_eq,
    bound, read, extend_byte, readFrame] using next

theorem write_body_wp (module_ : Wasm.Module) (host : HostEnv α) (initial : Store α)
    (bytes : ByteArray) (address value : UInt64)
    (represented : BytesAt bytes initial.mem) (valid : address.toNat < bytes.size)
    (Q : Assertion α)
    (next : Q (.Fallthrough (writeStore initial address value) (writeFrame address value))) :
    wp module_ writeFunction.body Q initial
      (writeFunction.toLocals [.i64 address, .i64 value]) host := by
  have bound : ¬initial.mem.pages * 65536 ≤ address.toNat % 4294967296 := by
    have := represented.size
    omega
  simpa [writeFunction, Function.toLocals, Locals.get, wrap_eq, wrap_byte,
    bound, writeStore, writeFrame] using next

theorem read_terminates {module_ : Wasm.Module} {id : Nat}
    (host : HostEnv α) (initial : Store α) (bytes : ByteArray) (address : UInt64)
    (notImported : module_.imports[id]? = none)
    (found : module_.funcs[id - module_.imports.length]? = some readFunction)
    (represented : BytesAt bytes initial.mem) (valid : address.toNat < bytes.size) :
    TerminatesWith host module_ id initial [.i64 address]
      (fun final values => final = initial ∧ values = [.i64 bytes[address.toNat]!.toUInt64]) := by
  apply Project.Core.invoke_of_wp (args := [address]) notImported found rfl rfl
  apply read_body_wp module_ host initial bytes address represented valid
  exact ⟨initial, readFrame address bytes[address.toNat]!.toUInt64, rfl, rfl, rfl⟩

theorem write_terminates {module_ : Wasm.Module} {id : Nat}
    (host : HostEnv α) (initial : Store α) (bytes : ByteArray) (address value : UInt64)
    (notImported : module_.imports[id]? = none)
    (found : module_.funcs[id - module_.imports.length]? = some writeFunction)
    (represented : BytesAt bytes initial.mem) (valid : address.toNat < bytes.size) :
    TerminatesWith host module_ id initial [.i64 value, .i64 address]
      (fun final values =>
        (final = writeStore initial address value ∧
          BytesAt (bytes.set! address.toNat value.toUInt8) final.mem) ∧ values = [.i64 0]) := by
  apply Project.Core.invoke_of_wp (args := [address, value]) notImported found rfl rfl
  apply write_body_wp module_ host initial bytes address value represented valid
  exact ⟨writeStore initial address value, writeFrame address value, rfl,
    ⟨rfl, writeStore_bytes represented address value valid⟩, rfl⟩

end Project.Core.ByteMemory
