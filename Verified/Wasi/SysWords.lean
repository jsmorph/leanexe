import Verified.Wasi.HostSpec

/-! The result words of a flat call: a word that the host leaves at a scratch address loads as
the little-endian value of the reply's output, and the regions of a call lie inside the scratch
area and the output buffer. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Runtime

theorem GuestFrame.cover {World : Type} {before after : Store World}
    {first second : List (Nat × Nat)} (h : GuestFrame before after first)
    (hCover : ∀ region ∈ first, ∃ outer ∈ second,
      outer.1 ≤ region.1 ∧ region.1 + region.2 ≤ outer.1 + outer.2) :
    GuestFrame before after second := by
  refine ⟨h.resources, h.pages, fun address hOutside => h.bytes address ?_⟩
  intro region hRegion hIn
  obtain ⟨outer, hOuter, hLow, hHigh⟩ := hCover region hRegion
  apply hOutside outer hOuter
  dsimp only [InRange] at hIn ⊢
  omega

private theorem or_add_shift {x y k : Nat} (hx : x < 2 ^ k) : x ||| y * 2 ^ k = x + y * 2 ^ k := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx, Nat.add_comm]

private theorem toNat_shiftLeft32 (x j : UInt32) (n : Nat) (hj : j.toNat = n) (hn : n < 32)
    (hx : x.toNat * 2 ^ n < 4294967296) : (x <<< j).toNat = x.toNat * 2 ^ n := by
  rw [UInt32.toNat_shiftLeft, hj, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn]
  exact Nat.mod_eq_of_lt hx

private theorem toNat_shiftLeft64 (x j : UInt64) (n : Nat) (hj : j.toNat = n) (hn : n < 64)
    (hx : x.toNat * 2 ^ n < 18446744073709551616) : (x <<< j).toNat = x.toNat * 2 ^ n := by
  rw [UInt64.toNat_shiftLeft, hj, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hn]
  exact Nat.mod_eq_of_lt hx

theorem toNat_read32 (m : Mem) (b : UInt32) :
    (m.read32 b).toNat = (m.bytes b.toNat).toNat + 256 * (m.bytes (b.toNat + 1)).toNat +
      65536 * (m.bytes (b.toNat + 2)).toNat + 16777216 * (m.bytes (b.toNat + 3)).toNat := by
  simp only [Mem.read32]
  generalize m.bytes b.toNat = b0
  generalize m.bytes (b.toNat + 1) = b1
  generalize m.bytes (b.toNat + 2) = b2
  generalize m.bytes (b.toNat + 3) = b3
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  simp only [Nat.reducePow] at h0 h1 h2 h3
  rw [UInt32.toNat_or, UInt32.toNat_or, UInt32.toNat_or,
    toNat_shiftLeft32 _ 8 8 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    toNat_shiftLeft32 _ 16 16 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    toNat_shiftLeft32 _ 24 24 rfl (by decide) (by rw [UInt8.toNat_toUInt32]; omega),
    UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32, UInt8.toNat_toUInt32,
    or_add_shift (x := b0.toNat) (y := b1.toNat) (k := 8) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8) (y := b2.toNat) (k := 16) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) (y := b3.toNat) (k := 24)
      (by omega)]
  omega

theorem toNat_read64 (m : Mem) (b : UInt32) :
    (m.read64 b).toNat = (m.bytes b.toNat).toNat + 256 * (m.bytes (b.toNat + 1)).toNat +
      65536 * (m.bytes (b.toNat + 2)).toNat + 16777216 * (m.bytes (b.toNat + 3)).toNat +
      4294967296 * (m.bytes (b.toNat + 4)).toNat +
      1099511627776 * (m.bytes (b.toNat + 5)).toNat +
      281474976710656 * (m.bytes (b.toNat + 6)).toNat +
      72057594037927936 * (m.bytes (b.toNat + 7)).toNat := by
  simp only [Mem.read64]
  generalize m.bytes b.toNat = b0
  generalize m.bytes (b.toNat + 1) = b1
  generalize m.bytes (b.toNat + 2) = b2
  generalize m.bytes (b.toNat + 3) = b3
  generalize m.bytes (b.toNat + 4) = b4
  generalize m.bytes (b.toNat + 5) = b5
  generalize m.bytes (b.toNat + 6) = b6
  generalize m.bytes (b.toNat + 7) = b7
  have h0 := b0.toNat_lt
  have h1 := b1.toNat_lt
  have h2 := b2.toNat_lt
  have h3 := b3.toNat_lt
  have h4 := b4.toNat_lt
  have h5 := b5.toNat_lt
  have h6 := b6.toNat_lt
  have h7 := b7.toNat_lt
  simp only [Nat.reducePow] at h0 h1 h2 h3 h4 h5 h6 h7
  rw [UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or, UInt64.toNat_or,
    UInt64.toNat_or, UInt64.toNat_or,
    toNat_shiftLeft64 _ 8 8 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 16 16 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 24 24 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 32 32 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 40 40 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 48 48 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    toNat_shiftLeft64 _ 56 56 rfl (by decide) (by rw [UInt8.toNat_toUInt64]; omega),
    UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64,
    UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64, UInt8.toNat_toUInt64,
    or_add_shift (x := b0.toNat) (y := b1.toNat) (k := 8) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8) (y := b2.toNat) (k := 16) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16) (y := b3.toNat) (k := 24)
      (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24)
      (y := b4.toNat) (k := 32) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
      b4.toNat * 2 ^ 32) (y := b5.toNat) (k := 40) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
      b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40) (y := b6.toNat) (k := 48) (by omega),
    or_add_shift (x := b0.toNat + b1.toNat * 2 ^ 8 + b2.toNat * 2 ^ 16 + b3.toNat * 2 ^ 24 +
      b4.toNat * 2 ^ 32 + b5.toNat * 2 ^ 40 + b6.toNat * 2 ^ 48) (y := b7.toNat) (k := 56)
      (by omega)]
  omega

private theorem byte_at {mem : Mem} {pointer : UInt64} {bytes : LeanExe.Bytes}
    (h : Bytes.At mem pointer bytes) {index : Nat} (hIndex : index < bytes.data.size) :
    (bytes.data[index]!).toNat = (mem.bytes (pointer.toNat + index)).toNat := by
  rw [h.contents index hIndex, getElem!_pos bytes.data index hIndex]

/-- A word of four bytes loads as the little-endian value of the bytes. -/
theorem littleEndian_read32 {mem : Mem} {pointer : UInt64} {bytes : LeanExe.Bytes}
    (h : Bytes.At mem pointer bytes) (hSize : bytes.data.size = 4) :
    UInt64.ofNat (mem.read32 pointer.toUInt32).toNat = littleEndian bytes := by
  have hAddress := h.address
  have hPointer : pointer.toUInt32.toNat = pointer.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have e0 := byte_at h (index := 0) (by omega)
  have e1 := byte_at h (index := 1) (by omega)
  have e2 := byte_at h (index := 2) (by omega)
  have e3 := byte_at h (index := 3) (by omega)
  have l0 := (bytes.data[0]!).toNat_lt
  have l1 := (bytes.data[1]!).toNat_lt
  have l2 := (bytes.data[2]!).toNat_lt
  have l3 := (bytes.data[3]!).toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [littleEndian, hSize, show List.range 4 = [0, 1, 2, 3] from rfl, List.foldr_cons,
    List.foldr_nil]
  rw [UInt64.toNat_ofNat_of_lt' (by
    rw [show UInt64.size = 18446744073709551616 from rfl]
    have := (mem.read32 pointer.toUInt32).toNat_lt
    omega), toNat_read32, hPointer]
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64, UInt64.reduceToNat]
  simp only [Nat.add_zero] at e0
  omega

/-- A word of eight bytes loads as the little-endian value of the bytes. -/
theorem littleEndian_read64 {mem : Mem} {pointer : UInt64} {bytes : LeanExe.Bytes}
    (h : Bytes.At mem pointer bytes) (hSize : bytes.data.size = 8) :
    mem.read64 pointer.toUInt32 = littleEndian bytes := by
  have hAddress := h.address
  have hPointer : pointer.toUInt32.toNat = pointer.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have e0 := byte_at h (index := 0) (by omega)
  have e1 := byte_at h (index := 1) (by omega)
  have e2 := byte_at h (index := 2) (by omega)
  have e3 := byte_at h (index := 3) (by omega)
  have e4 := byte_at h (index := 4) (by omega)
  have e5 := byte_at h (index := 5) (by omega)
  have e6 := byte_at h (index := 6) (by omega)
  have e7 := byte_at h (index := 7) (by omega)
  have l0 := (bytes.data[0]!).toNat_lt
  have l1 := (bytes.data[1]!).toNat_lt
  have l2 := (bytes.data[2]!).toNat_lt
  have l3 := (bytes.data[3]!).toNat_lt
  have l4 := (bytes.data[4]!).toNat_lt
  have l5 := (bytes.data[5]!).toNat_lt
  have l6 := (bytes.data[6]!).toNat_lt
  have l7 := (bytes.data[7]!).toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [littleEndian, hSize, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl,
    List.foldr_cons, List.foldr_nil]
  rw [toNat_read64, hPointer]
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64, UInt64.reduceToNat]
  simp only [Nat.add_zero] at e0
  omega

theorem littleEndian_four_lt {bytes : LeanExe.Bytes} (hSize : bytes.data.size = 4) :
    (littleEndian bytes).toNat < 4294967296 := by
  have l0 := (bytes.data[0]!).toNat_lt
  have l1 := (bytes.data[1]!).toNat_lt
  have l2 := (bytes.data[2]!).toNat_lt
  have l3 := (bytes.data[3]!).toNat_lt
  simp only [littleEndian, hSize, show List.range 4 = [0, 1, 2, 3] from rfl, List.foldr_cons,
    List.foldr_nil]
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64, UInt64.reduceToNat]
  omega

end Verified.Wasi
