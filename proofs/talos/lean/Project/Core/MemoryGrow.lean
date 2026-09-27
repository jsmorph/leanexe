import Project.Core.ByteMemory
import LeanExe.Core.Memory

namespace Project.Core.MemoryGrow

open Wasm
open LeanExe.Core.Memory

@[simp] theorem zeroBytes_size (count : Nat) : (zeroBytes count).size = count := by
  simp [zeroBytes, ByteArray.size]

theorem zeroBytes_get (count index : Nat) (valid : index < count) :
    (zeroBytes count)[index]! = 0 := by
  rw [getElem!_pos _ _ (by simpa using valid)]
  simp [zeroBytes, ByteArray.getElem_eq_getElem_data]

@[simp] theorem extend_size (bytes : ByteArray) (count : Nat) :
    (extend bytes count).size = bytes.size + count := by simp [extend]

theorem extend_old (bytes : ByteArray) (count index : Nat) (valid : index < bytes.size) :
    (extend bytes count)[index]! = bytes[index]! := by
  rw [getElem!_pos (extend bytes count) index (by simp; omega),
    getElem!_pos bytes index valid]
  exact ByteArray.getElem_append_left valid

theorem extend_new (bytes : ByteArray) (count index : Nat)
    (lower : bytes.size ≤ index) (upper : index < bytes.size + count) :
    (extend bytes count)[index]! = 0 := by
  rw [getElem!_pos (extend bytes count) index (by simpa using upper)]
  change (bytes ++ zeroBytes count)[index]'(by simpa using upper) = 0
  rw [ByteArray.getElem_append_right lower]
  have valid : index - bytes.size < count := by omega
  have zero := zeroBytes_get count (index - bytes.size) valid
  rw [getElem!_pos (zeroBytes count) (index - bytes.size) (by simpa using valid)] at zero
  exact zero

/-- Growth exposes zero-filled bytes. Talos retains the total byte function,
so the representation includes zeros beyond the current accessible range. -/
structure MemoryAt (bytes : ByteArray) (memory : Mem) : Prop
    extends ByteMemory.BytesAt bytes memory where
  zero : ∀ index, bytes.size ≤ index → memory.bytes index = 0

theorem MemoryAt.pages {bytes : ByteArray} {memory : Mem}
    (represented : MemoryAt bytes memory) : bytes.size / 65536 = memory.pages := by
  rw [represented.size]
  simp

theorem MemoryAt.empty (pages : Nat) (bounded : pages ≤ 65536) :
    MemoryAt (zeroBytes (pages * 65536)) (Mem.empty pages) := by
  refine ⟨⟨by simp [Mem.empty], by simp; omega, ?_⟩, ?_⟩
  · intro index valid
    simpa [Mem.empty] using (zeroBytes_get (pages * 65536) index (by simpa using valid)).symm
  · intro index _
    rfl

theorem MemoryAt.write {bytes : ByteArray} {memory : Mem}
    (represented : MemoryAt bytes memory) (address : UInt64) (value : UInt8)
    (valid : address.toNat < bytes.size) :
    MemoryAt (bytes.set! address.toNat value) (memory.write8 address.toUInt32 value) := by
  refine ⟨represented.toBytesAt.write address value valid, ?_⟩
  intro index outside
  have lower : bytes.size ≤ index := by simpa using outside
  have fits : address.toNat < 2 ^ 32 := Nat.lt_of_lt_of_le valid represented.bounded
  have different : index ≠ address.toNat := by omega
  simpa [Mem.write8, ByteMemory.address_toNat address fits, different] using
    represented.zero index lower

def grownMemory (memory : Mem) (delta : UInt64) : Mem :=
  { memory with pages := memory.pages + delta.toUInt32.toNat }

theorem MemoryAt.grow {bytes : ByteArray} {memory : Mem}
    (represented : MemoryAt bytes memory) (delta : UInt64)
    (bounded : memory.pages + delta.toUInt32.toNat ≤ 65536) :
    MemoryAt (extend bytes (delta.toUInt32.toNat * 65536)) (grownMemory memory delta) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [grownMemory, represented.size, Nat.add_mul]
  · rw [extend_size, represented.size, ← Nat.add_mul]
    omega
  · intro index valid
    by_cases old : index < bytes.size
    · rw [extend_old _ _ _ old]
      exact represented.byte index old
    · rw [extend_new _ _ _ (by omega) (by simpa using valid)]
      exact represented.zero index (by omega)
  · intro index outside
    apply represented.zero
    simp only [extend_size] at outside
    omega

def growStore (initial : Store α) (delta : UInt64) (cap : Nat) : Store α :=
  if initial.mem.pages + delta.toUInt32.toNat ≤ cap then
    { initial with mem := grownMemory initial.mem delta }
  else initial

theorem growStore_resources (initial : Store α) (delta : UInt64) (cap : Nat) :
    { growStore initial delta cap with mem := initial.mem } = initial := by
  unfold growStore
  split <;> rfl

theorem nativeGrow_represents {bytes : ByteArray} {initial : Store α}
    (represented : MemoryAt bytes initial.mem) (delta : UInt64) (cap : Nat)
    (bounded : cap ≤ 65536) :
    MemoryAt (nativeGrow bytes delta cap).2 (growStore initial delta cap).mem := by
  simp only [nativeGrow, growStore, represented.pages]
  split
  · exact represented.grow delta (by omega)
  · exact represented

def growFunction : Wasm.Function :=
  { params := [.i64]
    body := [.localGet 0, .wrapI64, .memoryGrow, .extendUI32]
    results := [.i64] }

def resultFrame (delta value : UInt64) : Locals :=
  { params := [.i64 delta], values := [.i64 value] }

private theorem wrap_eq (value : UInt64) :
    UInt32.ofNat (value.toNat % 4294967296) = value.toUInt32 := by
  apply UInt32.toNat.inj
  simp

private theorem extend_pages (pages : Nat) (bounded : pages ≤ 65536) :
    UInt64.ofNat (UInt32.ofNat pages).toNat = UInt64.ofNat pages := by
  rw [UInt32.toNat_ofNat_of_lt' (by change pages < 4294967296; omega)]

theorem grow_body_wp (module_ : Wasm.Module) (host : HostEnv α) (initial : Store α)
    (bytes : ByteArray) (delta : UInt64) (represented : MemoryAt bytes initial.mem)
    (bounded : initial.memoryCap module_ 0 ≤ 65536) (Q : Assertion α)
    (next : Q (.Fallthrough (growStore initial delta (initial.memoryCap module_ 0))
      (resultFrame delta (nativeGrow bytes delta (initial.memoryCap module_ 0)).1))) :
    wp module_ growFunction.body Q initial (growFunction.toLocals [.i64 delta]) host := by
  have oldBound : initial.mem.pages ≤ 65536 := by
    have := represented.size
    have := represented.bounded
    omega
  have resultEq := extend_pages initial.mem.pages oldBound
  have pagesFit : initial.mem.pages < 4294967296 := by omega
  by_cases available : initial.mem.pages + delta.toNat % 4294967296 ≤ initial.memoryCap module_ 0
  all_goals
    simpa [growFunction, Function.toLocals, Locals.get, wrap_eq, Mem.grow,
      nativeGrow, represented.pages, growStore, grownMemory, resultFrame,
      resultEq, Nat.mod_eq_of_lt pagesFit, available] using next

theorem grow_terminates {module_ : Wasm.Module} {id : Nat}
    (host : HostEnv α) (initial : Store α) (bytes : ByteArray) (delta : UInt64)
    (notImported : module_.imports[id]? = none)
    (found : module_.funcs[id - module_.imports.length]? = some growFunction)
    (represented : MemoryAt bytes initial.mem)
    (bounded : initial.memoryCap module_ 0 ≤ 65536) :
    TerminatesWith host module_ id initial [.i64 delta]
      (fun final values =>
        (final = growStore initial delta (initial.memoryCap module_ 0) ∧
          MemoryAt (nativeGrow bytes delta (initial.memoryCap module_ 0)).2 final.mem) ∧
        values = [.i64 (nativeGrow bytes delta (initial.memoryCap module_ 0)).1]) := by
  apply Project.Core.invoke_of_wp (args := [delta]) notImported found rfl rfl
  apply grow_body_wp module_ host initial bytes delta represented bounded
  exact ⟨growStore initial delta (initial.memoryCap module_ 0),
    resultFrame delta (nativeGrow bytes delta (initial.memoryCap module_ 0)).1, rfl,
    ⟨rfl, nativeGrow_represents represented delta _ bounded⟩, rfl⟩

end Project.Core.MemoryGrow
