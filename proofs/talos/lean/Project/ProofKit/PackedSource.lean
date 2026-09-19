import LeanExe.Packed
import Mathlib.Tactic

namespace Project.ProofKit.PackedSource

def pushWord (bytes : ByteArray) (word : UInt32) : ByteArray :=
  (((bytes.push word.toUInt8).push (word >>> 8).toUInt8).push
    (word >>> 16).toUInt8).push (word >>> 24).toUInt8

def wordPrefix (count : Nat) (value : Nat → UInt32) : ByteArray :=
  (List.range count).foldl (fun bytes index => pushWord bytes (value index)) ByteArray.empty

def wordByte (word : UInt32) (index : Nat) : UInt8 :=
  match index with
  | 0 => word.toUInt8
  | 1 => (word >>> 8).toUInt8
  | 2 => (word >>> 16).toUInt8
  | _ => (word >>> 24).toUInt8

theorem generate_eq_wordPrefix (count : Nat) (value : Nat → UInt32) :
    LeanExe.Packed.generateUInt32LE count value = wordPrefix count value := by
  simp [LeanExe.Packed.generateUInt32LE, wordPrefix, pushWord,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, List.range_eq_range']
  rfl

@[simp] theorem wordPrefix_zero (value : Nat → UInt32) : wordPrefix 0 value = ByteArray.empty := rfl

theorem wordPrefix_succ (count : Nat) (value : Nat → UInt32) :
    wordPrefix (count + 1) value = pushWord (wordPrefix count value) (value count) := by
  simp [wordPrefix, List.range_succ]

@[simp] theorem pushWord_size (bytes : ByteArray) (word : UInt32) :
    (pushWord bytes word).size = bytes.size + 4 := by
  simp [pushWord, ByteArray.size_push]

@[simp] theorem wordPrefix_size (count : Nat) (value : Nat → UInt32) :
    (wordPrefix count value).size = 4 * count := by
  induction count with
  | zero => simp
  | succ count ih => rw [wordPrefix_succ, pushWord_size, ih]; omega

theorem pushWord_before (bytes : ByteArray) (word : UInt32) (index : Nat)
    (hindex : index < bytes.size) : (pushWord bytes word)[index]! = bytes[index]! := by
  simp only [pushWord]
  repeat rw [ByteArray.getElem!_push_lt _ _ _ (by first | exact hindex | (simp only [ByteArray.size_push]; omega))]

theorem pushWord_byte (bytes : ByteArray) (word : UInt32) (index : Nat)
    (hindex : index < 4) :
    (pushWord bytes word)[bytes.size + index]! = wordByte word index := by
  interval_cases index <;>
    simp only [pushWord, wordByte, ByteArray.getElem!_push, ByteArray.size_push]
  all_goals split_ifs <;> first | rfl | omega

theorem wordPrefix_byte (count : Nat) (value : Nat → UInt32) (index byte : Nat)
    (hindex : index < count) (hbyte : byte < 4) :
    (wordPrefix count value)[4 * index + byte]! = wordByte (value index) byte := by
  induction count with
  | zero => omega
  | succ count ih =>
    rw [wordPrefix_succ]
    by_cases hlast : index = count
    · subst index
      rw [← wordPrefix_size count value]
      exact pushWord_byte _ _ byte hbyte
    · rw [pushWord_before _ _ _ (by rw [wordPrefix_size]; omega)]
      exact ih (by omega)

theorem generate_size (count : Nat) (value : Nat → UInt32) :
    (LeanExe.Packed.generateUInt32LE count value).size = 4 * count := by
  rw [generate_eq_wordPrefix, wordPrefix_size]

theorem generate_byte (count : Nat) (value : Nat → UInt32) (index byte : Nat)
    (hindex : index < count) (hbyte : byte < 4) :
    (LeanExe.Packed.generateUInt32LE count value)[4 * index + byte]! =
      wordByte (value index) byte := by
  rw [generate_eq_wordPrefix]
  exact wordPrefix_byte count value index byte hindex hbyte

theorem assemble_word (word : UInt32) :
    word.toUInt8.toUInt32 ||| ((word >>> 8).toUInt8.toUInt32 <<< 8) |||
      ((word >>> 16).toUInt8.toUInt32 <<< 16) |||
      ((word >>> 24).toUInt8.toUInt32 <<< 24) = word := by
  apply UInt32.toBitVec_inj.mp
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt8.toBitVec_toUInt32, UInt32.toBitVec_toUInt8]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  interval_cases bit <;> simp [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']

theorem generate_read (count : Nat) (value : Nat → UInt32) (index : Nat)
    (hindex : index < count) :
    LeanExe.Packed.getUInt32LE! (LeanExe.Packed.generateUInt32LE count value)
      (4 * index) = value index := by
  have hfit : 4 * index + 4 ≤ (LeanExe.Packed.generateUInt32LE count value).size := by
    rw [generate_size]
    omega
  have h0 := generate_byte count value index 0 hindex (by decide)
  have h1 := generate_byte count value index 1 hindex (by decide)
  have h2 := generate_byte count value index 2 hindex (by decide)
  have h3 := generate_byte count value index 3 hindex (by decide)
  simp only [Nat.add_zero] at h0
  simp only [LeanExe.Packed.getUInt32LE!, ite_eq_left hfit, h0, h1, h2, h3, wordByte]
  exact assemble_word (value index)

#print axioms generate_size
#print axioms generate_byte
#print axioms generate_read

end Project.ProofKit.PackedSource
