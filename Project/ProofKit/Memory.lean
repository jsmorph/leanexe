import Project.TalosPrelude
import Project.TalosCompat

namespace Project.ProofKit.Memory

open Wasm

theorem toUInt32_toNat (x : UInt64) :
    x.toUInt32.toNat = x.toNat % 4294967296 := by
  simp

theorem toNat_ofNat_lt {n : Nat} (h : n < UInt64.size) :
    (UInt64.ofNat n).toNat = n :=
  UInt64.toNat_ofNat_of_lt' h

theorem toUInt32_eq_ofNat (x : UInt64) :
    x.toUInt32 = UInt32.ofNat (x.toNat % 4294967296) := by
  apply UInt32.toNat.inj
  simp

theorem toNat_sub_of_le (value offset : UInt64)
    (h : offset.toNat ≤ value.toNat) :
    (value - offset).toNat = value.toNat - offset.toNat := by
  rw [UInt64.toNat_sub]
  have hValue := value.toNat_lt_size
  have hOffset := offset.toNat_lt_size
  have hSize : UInt64.size = 18446744073709551616 := rfl
  omega

theorem read64_congr {m1 m2 : Mem} (address : UInt32)
    (h : ∀ i : Nat, i < 8 →
      m1.bytes (address.toNat + i) = m2.bytes (address.toNat + i)) :
    m1.read64 address = m2.read64 address := by
  have h0 := h 0 (by omega)
  have h1 := h 1 (by omega)
  have h2 := h 2 (by omega)
  have h3 := h 3 (by omega)
  have h4 := h 4 (by omega)
  have h5 := h 5 (by omega)
  have h6 := h 6 (by omega)
  have h7 := h 7 (by omega)
  rw [Nat.add_zero] at h0
  simp only [Mem.read64]
  rw [h0, h1, h2, h3, h4, h5, h6, h7]

theorem write64_bytes_before (mem : Mem) (address : UInt32) (value : UInt64)
    {index : Nat} (h : index < address.toNat) :
    (mem.write64 address value).bytes index = mem.bytes index := by
  unfold Mem.write64
  dsimp only
  split_ifs <;> first | rfl | omega

theorem write64_bytes_outside (mem : Mem) (address : UInt32) (value : UInt64)
    {index : Nat} (h : index < address.toNat ∨ address.toNat + 8 ≤ index) :
    (mem.write64 address value).bytes index = mem.bytes index := by
  unfold Mem.write64
  dsimp only
  split_ifs <;> first | rfl | omega

theorem read64_write64_disjoint (mem : Mem) (writeAddress : UInt32)
    (value : UInt64) (readAddress : UInt32)
    (h : readAddress.toNat + 8 ≤ writeAddress.toNat ∨
      writeAddress.toNat + 8 ≤ readAddress.toNat) :
    (mem.write64 writeAddress value).read64 readAddress =
      mem.read64 readAddress :=
  read64_congr readAddress fun i hi => write64_bytes_outside mem writeAddress value (by omega)

/-- Reading a word back from the address it was written to returns the value,
checked by the kernel bit by bit. -/
theorem read64_write64 (mem : Mem) (address : UInt32) (value : UInt64) :
    (mem.write64 address value).read64 address = value := by
  simp only [Mem.read64, Mem.write64]
  simp only [Nat.add_eq_left, OfNat.ofNat_ne_zero, Nat.succ_ne_self, reduceIte,
    Nat.reduceEqDiff]
  apply UInt64.toBitVec_inj.mp
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_and, UInt8.toBitVec_toUInt64, UInt64.toBitVec_toUInt8]
  apply BitVec.eq_of_getLsbD_eq
  intro bit hbit
  interval_cases bit <;> simp [BitVec.shiftLeft_eq', BitVec.ushiftRight_eq']

macro "word_reads" : tactic =>
  `(tactic|
    repeat first
      | rw [read64_write64]
      | rw [Project.ProofKit.Memory.read64_write64_disjoint _ _ _ _ (by omega)])

end Project.ProofKit.Memory
