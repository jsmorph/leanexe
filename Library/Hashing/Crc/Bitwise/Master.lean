import Library.Hashing.Crc.Bitwise.Compiled
import Verified.Master

namespace Library.Hashing.Crc.Bitwise

open Polynomial Library.Hashing.Crc Library.Bytes

/-- For `r < 2 ^ 32`, bit `i` of `crc32Reg r b` is the coefficient of `x^(31 - i)` in the
remainder of `x^8 R + x^32 B` divided by CRC-32's generator, where `R` is the polynomial of the 32
bits of `r` and `B` that of the low 8 bits of `b`, each with its least significant bit as the
highest coefficient. -/
theorem crc32Reg_poly (r b : UInt64) (hr : r.toNat < 2 ^ 32) :
    (crc32Reg r b).toNat = Spec.value ((X ^ 8 * Spec.poly ((List.range 32).map r.toNat.testBit) +
      X ^ 32 * Spec.poly ((List.range 8).map b.toNat.testBit)) %ₘ Spec.g32) := by
  have h := Proof.byteStep_holds (Division.length_lowBits _) Proof.crc32Table_of
    (r := r) (S := Proof.natBits 32 r.toNat) ⟨hr, rfl⟩ b
  have hS : (Division.lfsr (Division.lowBits 0x04C11DB7) (Proof.natBits 32 r.toNat)
      (Proof.natBits 8 b.toNat)).length = 32 :=
    Division.length_lfsr _ (Division.length_lowBits _) _ _ (Proof.length_natBits _ _)
  rw [crc32Reg_eq, Proof.toNat_eq_bitsValue h, ← Division.value_poly _ hS,
    Division.lfsr_spec _ (Division.length_lowBits _) _ _ (Proof.length_natBits _ _),
    Proof.length_natBits, Division.g32_eq]
  rfl

/-- The export `crc32Reg`, called on a register `r < 2 ^ 32` and a word `b`, returns the word
whose bit `i` is the coefficient of `x^(31 - i)` in the remainder of `x^8 R + x^32 B` divided by
the CRC-32 generator of ITU-T V.42, where `R` is the polynomial of the 32 bits of `r` and `B` that
of the low 8 bits of `b`, each with its least significant bit as the highest coefficient. -/
theorem crc32Reg_master :
    Verified.Master compiled.module compiled.tables "crc32Reg" compiled.crc32Reg.bound
      (fun x : UInt64 × UInt64 => x.1.toNat < 2 ^ 32)
      (fun x (y : UInt64) => y.toNat = Spec.value
        ((X ^ 8 * Spec.poly ((List.range 32).map x.1.toNat.testBit) +
          X ^ 32 * Spec.poly ((List.range 8).map x.2.toNat.testBit)) %ₘ Spec.g32)) :=
  .of_trapFree (.ofA compiled.crc32Reg.trapFree) nofun crc32Reg_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ hr => crc32Reg_poly x.1 x.2 hr

#print axioms crc32Reg_master

/-- The export `crc32Byte`, called on a word `crc` that is CRC-32 of some bytes and a word `b`,
returns, for all bytes `A` whose CRC-32 is `crc`, CRC-32 of `A` followed by the low byte of `b`. -/
theorem crc32Byte_master :
    Verified.Master compiled.module compiled.tables "crc32Byte" compiled.crc32Byte.bound
      (fun x : UInt64 × UInt64 => ∃ A, x.1.toNat = Spec.crc32 A)
      (fun x (y : UInt64) => ∀ A, x.1.toNat = Spec.crc32 A →
        y.toNat = Spec.crc32 (A ++ [x.2.toUInt8])) :=
  .of_trapFree (.ofA compiled.crc32Byte.trapFree) nofun crc32Byte_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ A hA => crc32Byte_spec A x.1 hA x.2

#print axioms crc32Byte_master

/-- The export `crc32Word`, called on a word `crc` that is CRC-32 of some bytes, a word `w`, and a
count `n`, returns, for all bytes `A` whose CRC-32 is `crc`, CRC-32 of `A` followed by the first
`min n 8` bytes of `w` from the most significant. -/
theorem crc32Word_master :
    Verified.Master compiled.module compiled.tables "crc32Word" compiled.crc32Word.bound
      (fun x : UInt64 × UInt64 × UInt64 => ∃ A, x.1.toNat = Spec.crc32 A)
      (fun x (y : UInt64) => ∀ A, x.1.toNat = Spec.crc32 A →
        y.toNat = Spec.crc32
          (A ++ (List.range (min x.2.2.toNat 8)).map fun i => byteOf x.2.1 (7 - i))) :=
  .of_trapFree (.ofA compiled.crc32Word.trapFree) nofun crc32Word_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ x _ _ A hA => by
      rw [crc32Word_spec A x.1 hA x.2.1 x.2.2, wordBytes_map _ _ (Nat.min_le_right _ _)]

#print axioms crc32Word_master

end Library.Hashing.Crc.Bitwise
