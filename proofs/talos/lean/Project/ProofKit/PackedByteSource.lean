import LeanExe.Packed
import Mathlib.Tactic

namespace Project.ProofKit.PackedByteSource

def bytePrefix (count : Nat) (value : Nat → UInt8) : ByteArray :=
  (List.range count).foldl (fun bytes index => bytes.push (value index)) ByteArray.empty

theorem generate_eq_bytePrefix (count : Nat) (value : Nat → UInt8) :
    LeanExe.Packed.generateUInt8 count value = bytePrefix count value := by
  simp [LeanExe.Packed.generateUInt8, bytePrefix,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, List.range_eq_range']
  rfl

@[simp] theorem bytePrefix_zero (value : Nat → UInt8) : bytePrefix 0 value = ByteArray.empty := rfl

theorem bytePrefix_succ (count : Nat) (value : Nat → UInt8) :
    bytePrefix (count + 1) value = (bytePrefix count value).push (value count) := by
  simp [bytePrefix, List.range_succ]

@[simp] theorem bytePrefix_size (count : Nat) (value : Nat → UInt8) :
    (bytePrefix count value).size = count := by
  induction count with
  | zero => rfl
  | succ count ih => rw [bytePrefix_succ, ByteArray.size_push, ih]

theorem bytePrefix_byte (count : Nat) (value : Nat → UInt8) (index : Nat)
    (hindex : index < count) : (bytePrefix count value)[index]! = value index := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [bytePrefix_succ]
    by_cases hlast : index = count
    · subst index
      simp only [ByteArray.getElem!_push, bytePrefix_size, ↓reduceIte]
    · rw [ByteArray.getElem!_push_lt _ _ _ (by rw [bytePrefix_size]; omega)]
      exact ih (by omega)

theorem generate_size (count : Nat) (value : Nat → UInt8) :
    (LeanExe.Packed.generateUInt8 count value).size = count := by
  rw [generate_eq_bytePrefix, bytePrefix_size]

theorem generate_byte (count : Nat) (value : Nat → UInt8) (index : Nat)
    (hindex : index < count) :
    (LeanExe.Packed.generateUInt8 count value)[index]! = value index := by
  rw [generate_eq_bytePrefix, bytePrefix_byte count value index hindex]

end Project.ProofKit.PackedByteSource
