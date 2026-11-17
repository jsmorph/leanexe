import Verified.Shim.Strings
import LeanExe.A64.Proof.WasiStrings

/-!
The shim's `sizesInvoke` and `stringsInvoke` in the terms of the runs of the stubs of
`LeanExe/A64/WasiStrings.lean`.  `vectorSize` and the bytes that the copying pass writes are the
specification's `stringsSize` and `stringsBytes` by definition, `pointerBytes` from the buffer's
address is `stringPointers`, and the bytes that `store32` stores of a count or a size are those of
`leBytes 4`.  `sizesInvoke_eq` and `stringsInvoke_eq` state the two functions for a memory of at
most 65,535 pages, the bound that `StoreRel` gives, at which the tests against `2^32` follow from
the tests against the memory's size: the trap with the store unchanged, errno 61, the count and
the size written, or the addresses and the strings written, and the trap with the event of a
count or a size of `2^32` or more.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

theorem vectorSize_eq (strs : List (List UInt8)) : vectorSize strs = stringsSize strs := rfl

theorem flatMap_zero_eq (strs : List (List UInt8)) :
    strs.flatMap (· ++ [0]) = stringsBytes strs := rfl

theorem stringsFit_iff (strs : List (List UInt8)) :
    stringsFit strs = true ↔ stringsSize strs < 2 ^ 32 := by
  have := length_le_vectorSize strs
  rw [vectorSize_eq] at this
  simp only [stringsFit, decide_eq_true_eq]
  omega

/-- Byte `k` of a word of eight bytes holding `n` is byte `k` of `n`. -/
theorem shift_byte (n k : Nat) (hk : k < 8) :
    ((UInt64.ofNat n) >>> UInt64.ofNat (8 * k)).toUInt8 = Verified.Wasi.byteOf n k := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Verified.Wasi.byteOf, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * k < 64 by omega)]
  have e : 2 ^ 64 = 2 ^ (8 * k) * 2 ^ (64 - 8 * k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [e, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 ≤ 64 - 8 * k))]

/-- The bytes that four `STRB` store of the low 32 bits of a number are its four little-endian
bytes. -/
theorem word32Bytes_ofNat (n : Nat) :
    word32Bytes (UInt64.ofNat n) = (List.range 4).map (Verified.Wasi.byteOf n) := by
  show [_, _, _, _] = [Verified.Wasi.byteOf n 0, Verified.Wasi.byteOf n 1,
    Verified.Wasi.byteOf n 2, Verified.Wasi.byteOf n 3]
  have e0 := shift_byte n 0 (by decide)
  rw [Nat.mul_zero, show UInt64.ofNat 0 = 0 from rfl, UInt64.shiftRight_zero] at e0
  rw [e0, ← shift_byte n 1 (by decide), ← shift_byte n 2 (by decide),
    ← shift_byte n 3 (by decide)]

theorem leBytes_list (n : Nat) :
    (leBytes 4 n).data.data.toList = word32Bytes (UInt64.ofNat n) := by
  rw [word32Bytes_ofNat]
  rfl

/-- `stringPointers` from the buffer at `b` is `pointerBytes` from its address. -/
theorem pointerBytes_ofNat : ∀ (b : Nat) (strs : List (List UInt8)),
    pointerBytes (UInt64.ofNat b) strs = stringPointers b strs
  | _, [] => rfl
  | b, s :: rest => by
    rw [pointerBytes, stringPointers, word32Bytes_ofNat, ← UInt64.ofNat_add,
      pointerBytes_ofNat (b + (s.length + 1)) rest, Nat.add_assoc]

/-- `sizesInvoke` for a memory of at most 65,535 pages: the trap with the store unchanged when
either result's four bytes leave the memory, and otherwise errno 0 with the count and the size
written in that order, or errno 61 with the memory unchanged when the size reaches `2^32`. -/
theorem sizesInvoke_eq (strings : List (List UInt8)) (call : Call)
    (before : Store (Observed LinuxWorld)) (count size : UInt32)
    (hpages : before.mem.pages < 65536) :
    sizesInvoke strings call before [.i32 count, .i32 size] =
      if count.toNat + 4 ≤ before.mem.pages * 65536 ∧
          size.toNat + 4 ≤ before.mem.pages * 65536 then
        if stringsSize strings < 2 ^ 32 then
          .Return [.i32 0] (answered before
            ((before.mem.writeBytes count.toNat
              (word32Bytes (UInt64.ofNat strings.length))).writeBytes
              size.toNat (word32Bytes (UInt64.ofNat (stringsSize strings))))
            [] (.sys call [] (sizesReply strings)))
        else .Return [.i32 61] (answered before before.mem [] (.sys call [] (sizesReply strings)))
      else .Trap before shimTrap := by
  unfold sizesInvoke
  dsimp only
  by_cases hc : count.toNat + 4 ≤ before.mem.pages * 65536 ∧
      size.toNat + 4 ≤ before.mem.pages * 65536
  · rw [ite_eq_left ⟨hc.1, by omega, hc.2, by omega⟩, ite_eq_left hc]
    by_cases hfit : stringsSize strings < 2 ^ 32
    · have hf : stringsFit strings = true := (stringsFit_iff strings).mpr hfit
      rw [ite_eq_left hfit]
      simp only [sysAnswer, sizesReply, hf, ↓reduceIte, placeReply, sysResult, sizesOutputs,
        placeAll, leBytes_list, List.headD, List.getD_cons_succ, List.getD_cons_zero]
      rfl
    · have hf : stringsFit strings = false := by
        cases h : stringsFit strings
        · rfl
        · exact absurd ((stringsFit_iff strings).mp h) hfit
      rw [ite_eq_right hfit]
      simp only [sysAnswer, sizesReply, hf, Bool.false_eq_true, ↓reduceIte, placeReply,
        sysResult]
      rfl
  · rw [ite_eq_right (fun h => hc ⟨h.1, h.2.2.1⟩), ite_eq_right hc]

/-- `stringsInvoke` for a memory of at most 65,535 pages: the trap with the event of the call when
the size reaches `2^32`, the trap with the store unchanged when the array or the buffer leaves the
memory, and otherwise errno 0 with the addresses and then the strings written. -/
theorem stringsInvoke_eq (strings : List (List UInt8)) (call : Call)
    (before : Store (Observed LinuxWorld)) (argv buf : UInt32)
    (hpages : before.mem.pages < 65536) :
    stringsInvoke strings call before [.i32 argv, .i32 buf] =
      if stringsSize strings < 2 ^ 32 then
        if argv.toNat + 4 * strings.length ≤ before.mem.pages * 65536 ∧
            buf.toNat + stringsSize strings ≤ before.mem.pages * 65536 then
          .Return [.i32 0] (answered before
            ((before.mem.writeBytes argv.toNat (stringPointers buf.toNat strings)).writeBytes
              buf.toNat (stringsBytes strings))
            [] (.sys call [] (stringsReply strings)))
        else .Trap before shimTrap
      else
        .Trap (answered before before.mem [] (.sys call [] (stringsReply strings))) shimTrap := by
  unfold stringsInvoke
  dsimp only
  by_cases hfit : stringsSize strings < 2 ^ 32
  · have hf : stringsFit strings = true := (stringsFit_iff strings).mpr hfit
    rw [ite_eq_left hf, ite_eq_left hfit]
    by_cases hc : argv.toNat + 4 * strings.length ≤ before.mem.pages * 65536 ∧
        buf.toNat + stringsSize strings ≤ before.mem.pages * 65536
    · rw [ite_eq_left ⟨hc.1, by omega, hc.2, by omega⟩, ite_eq_left hc]
      simp only [sysAnswer, stringsReply, hf, ↓reduceIte, sysResult]
      rfl
    · rw [ite_eq_right (fun h => hc ⟨h.1, h.2.2.1⟩), ite_eq_right hc]
  · have hf : stringsFit strings = false := by
      cases h : stringsFit strings
      · rfl
      · exact absurd ((stringsFit_iff strings).mp h) hfit
    rw [ite_eq_right (by rw [hf]; decide), ite_eq_right hfit]
    simp only [sysAnswer, stringsReply, hf, Bool.false_eq_true, ↓reduceIte, sysResult]

end Verified.ShimA64
