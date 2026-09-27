import LeanExe.Core.Memory
import Project.Core.MemoryGrow

namespace Project.Core.Memory

open Wasm
open ByteMemory (BytesAt)

def boundsCode : Wasm.Program :=
  [.localGet 0, .memorySize, .extendUI32, .constI64 65536, .mulI64, .ltUI64]

def readFunction : Wasm.Function :=
  { params := [.i64]
    body := boundsCode ++ [.iff 0 1
      [.localGet 0, .wrapI64, .load8U 0, .extendUI32] [.constI64 0] [] [.i64]]
    results := [.i64]
    typeIdx := some 1 }

def writeFunction : Wasm.Function :=
  { params := [.i64, .i64]
    body := boundsCode ++ [.iff 0 0
      [.localGet 0, .wrapI64, .localGet 1, .wrapI64, .store8 0] [], .constI64 0]
    results := [.i64]
    typeIdx := some 2 }

def sizeFunction : Wasm.Function :=
  { body := [.memorySize, .extendUI32, .constI64 65536, .mulI64]
    results := [.i64]
    typeIdx := some 0 }

def writeStore (initial : Store α) (address value : UInt64) : Store α :=
  if address.toNat < initial.mem.pages * 65536 then
    ByteMemory.writeStore initial address value else initial

private theorem capacity_eq {bytes : ByteArray} {memory : Mem}
    (represented : BytesAt bytes memory) :
    UInt64.ofNat (UInt32.ofNat memory.pages).toNat * 65536 = UInt64.ofNat bytes.size := by
  have pagesFit : memory.pages < 4294967296 := by
    have := represented.size
    have := represented.bounded
    omega
  rw [UInt32.toNat_ofNat_of_lt' pagesFit, represented.size, UInt64.ofNat_mul]
  rfl

private theorem size_fits {bytes : ByteArray} {memory : Mem}
    (represented : BytesAt bytes memory) : bytes.size < 18446744073709551616 := by
  have := represented.bounded
  omega

private theorem capacity_nat {bytes : ByteArray} {memory : Mem}
    (represented : BytesAt bytes memory) :
    memory.pages % 4294967296 * 65536 % 18446744073709551616 = bytes.size := by
  have pagesFit : memory.pages < 4294967296 := by
    have := represented.size
    have := represented.bounded
    omega
  rw [Nat.mod_eq_of_lt pagesFit, ← represented.size]
  exact Nat.mod_eq_of_lt (size_fits represented)

private theorem wrap_eq (value : UInt64) :
    UInt32.ofNat (value.toNat % 4294967296) = value.toUInt32 := by
  apply UInt32.toNat.inj
  simp

private theorem wrap_byte (value : UInt64) :
    UInt8.ofNat (value.toNat % 4294967296) = value.toUInt8 := by
  apply UInt8.toNat.inj
  simp only [UInt8.toNat_ofNat', UInt64.toNat_toUInt8, Nat.reducePow]
  omega

theorem read_body_wp (module_ : Wasm.Module) (host : HostEnv α) (initial : Store α)
    (bytes : ByteArray) (address : UInt64)
    (represented : BytesAt bytes initial.mem) (memory32 : module_.memIs64 = false)
    (Q : Assertion α)
    (next : Q (.Fallthrough initial
      (ByteMemory.readFrame address (LeanExe.Core.Memory.read address bytes).1))) :
    wp module_ readFunction.body Q initial (readFunction.toLocals [.i64 address]) host := by
  have capacity := capacity_nat represented
  have fits := size_fits represented
  by_cases valid : address.toNat < bytes.size
  · have access := represented.access address valid
    have read := represented.read address valid
    have bound : ¬ initial.mem.pages * 65536 ≤ address.toNat % 4294967296 := by
      have addressFit : address.toNat < 4294967296 := by have := represented.bounded; omega
      rw [Nat.mod_eq_of_lt addressFit, ← represented.size]
      omega
    simp [wp_simp, readFunction, boundsCode, Function.toLocals, Locals.get, memory32,
      sizeValue, UInt64.lt_iff_toNat_lt, capacity, valid]
    apply wp_iff_cons rfl
    simpa [wp_simp, LeanExe.Core.Memory.read, valid, Locals.get,
      wrap_eq, bound, read, ByteMemory.readFrame] using next
  · simp [wp_simp, readFunction, boundsCode, Function.toLocals, Locals.get, memory32,
      sizeValue, UInt64.lt_iff_toNat_lt, capacity, valid]
    apply wp_iff_cons rfl
    simpa [wp_simp, LeanExe.Core.Memory.read, valid, ByteMemory.readFrame] using next

theorem write_represents {bytes : ByteArray} {initial : Store α}
    (represented : MemoryGrow.MemoryAt bytes initial.mem) (address value : UInt64) :
    MemoryGrow.MemoryAt (LeanExe.Core.Memory.write address value bytes).2
      (writeStore initial address value).mem := by
  simp only [LeanExe.Core.Memory.write, writeStore, ← represented.size]
  split
  · exact represented.write address value.toUInt8 (by assumption)
  · exact represented

theorem write_body_wp (module_ : Wasm.Module) (host : HostEnv α) (initial : Store α)
    (bytes : ByteArray) (address value : UInt64)
    (represented : BytesAt bytes initial.mem) (memory32 : module_.memIs64 = false)
    (Q : Assertion α)
    (next : Q (.Fallthrough (writeStore initial address value)
      (ByteMemory.writeFrame address value))) :
    wp module_ writeFunction.body Q initial
      (writeFunction.toLocals [.i64 address, .i64 value]) host := by
  have capacity := capacity_nat represented
  have fits := size_fits represented
  by_cases valid : address.toNat < bytes.size
  · have bound : ¬ initial.mem.pages * 65536 ≤ address.toNat % 4294967296 := by
      have addressFit : address.toNat < 4294967296 := by have := represented.bounded; omega
      rw [Nat.mod_eq_of_lt addressFit, ← represented.size]
      omega
    simp [wp_simp, writeFunction, boundsCode, Function.toLocals, Locals.get, memory32,
      sizeValue, UInt64.lt_iff_toNat_lt, capacity, valid]
    apply wp_iff_cons rfl
    have byteBound : ¬ bytes.size ≤ address.toNat % 4294967296 := by
      simpa only [represented.size] using bound
    simpa [wp_simp, Locals.get, writeStore, ← represented.size, valid,
      wrap_eq, wrap_byte, byteBound, ByteMemory.writeStore, ByteMemory.writeFrame] using next
  · simp [wp_simp, writeFunction, boundsCode, Function.toLocals, Locals.get, memory32,
      sizeValue, UInt64.lt_iff_toNat_lt, capacity, valid]
    apply wp_iff_cons rfl
    simpa [wp_simp, writeStore, ← represented.size, valid, ByteMemory.writeFrame] using next

theorem size_body_wp (module_ : Wasm.Module) (host : HostEnv α) (initial : Store α)
    (bytes : ByteArray) (represented : BytesAt bytes initial.mem)
    (memory32 : module_.memIs64 = false) (Q : Assertion α)
    (next : Q (.Fallthrough initial { values := [.i64 (UInt64.ofNat bytes.size)] })) :
    wp module_ sizeFunction.body Q initial (sizeFunction.toLocals []) host := by
  have capacity : UInt64.ofNat (initial.mem.pages % 4294967296) * 65536 =
      UInt64.ofNat bytes.size := by simpa using capacity_eq represented
  simpa [sizeFunction, Function.toLocals, memory32, sizeValue, capacity] using next

theorem read_terminates {module_ : Wasm.Module} {id : Nat}
    (host : HostEnv α) (initial : Store α) (bytes : ByteArray) (address : UInt64)
    (notImported : module_.imports[id]? = none)
    (found : module_.funcs[id - module_.imports.length]? = some readFunction)
    (represented : BytesAt bytes initial.mem) (memory32 : module_.memIs64 = false) :
    TerminatesWith host module_ id initial [.i64 address]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Core.Memory.read address bytes).1]) := by
  apply invoke_of_wp (args := [address]) notImported found rfl rfl
  apply read_body_wp module_ host initial bytes address represented memory32
  exact ⟨initial, _, rfl, rfl, rfl⟩

theorem write_terminates {module_ : Wasm.Module} {id : Nat}
    (host : HostEnv α) (initial : Store α) (bytes : ByteArray) (address value : UInt64)
    (notImported : module_.imports[id]? = none)
    (found : module_.funcs[id - module_.imports.length]? = some writeFunction)
    (represented : MemoryGrow.MemoryAt bytes initial.mem) (memory32 : module_.memIs64 = false) :
    TerminatesWith host module_ id initial [.i64 value, .i64 address]
      (fun final values =>
        (final = writeStore initial address value ∧
          MemoryGrow.MemoryAt (LeanExe.Core.Memory.write address value bytes).2 final.mem) ∧
        values = [.i64 0]) := by
  apply invoke_of_wp (args := [address, value]) notImported found rfl rfl
  apply write_body_wp module_ host initial bytes address value represented.toBytesAt memory32
  exact ⟨writeStore initial address value, _, rfl,
    ⟨rfl, write_represents represented address value⟩, rfl⟩

theorem size_terminates {module_ : Wasm.Module} {id : Nat}
    (host : HostEnv α) (initial : Store α) (bytes : ByteArray)
    (notImported : module_.imports[id]? = none)
    (found : module_.funcs[id - module_.imports.length]? = some sizeFunction)
    (represented : BytesAt bytes initial.mem) (memory32 : module_.memIs64 = false) :
    TerminatesWith host module_ id initial []
      (fun final values => final = initial ∧ values = [.i64 (UInt64.ofNat bytes.size)]) := by
  apply invoke_of_wp (args := []) notImported found rfl rfl
  apply size_body_wp module_ host initial bytes represented memory32
  exact ⟨initial, _, rfl, rfl, rfl⟩

end Project.Core.Memory
