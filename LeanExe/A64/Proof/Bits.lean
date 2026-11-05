import LeanExe.A64.Machine

/-!
Arithmetic facts about the bitwise definitions of the AArch64 model: `load64` is the
little-endian sum of its eight bytes, a `load64` after a `store64` at the same address reads the
stored word and one at least 8 bytes away reads what it read before, and a `MOVK` into a value
below `2 ^ sh` adds its field.  The proofs turn an OR of disjoint fields into a sum with
`Nat.two_pow_add_eq_or_of_lt` and use no bit-vector decision procedure.
-/

namespace LeanExe.A64

/-- An OR of `x` with a multiple of `2 ^ i` above it is their sum. -/
theorem or_mul_two_pow {x b i : Nat} (hx : x < 2 ^ i) : x ||| b * 2 ^ i = x + b * 2 ^ i := by
  rw [Nat.or_comm, Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hx b]
  omega

/-- Eight bytes ORed at their positions are their little-endian sum. -/
theorem or8 {b0 b1 b2 b3 b4 b5 b6 : Nat} (b7 : Nat) (h0 : b0 < 256) (h1 : b1 < 256)
    (h2 : b2 < 256) (h3 : b3 < 256) (h4 : b4 < 256) (h5 : b5 < 256) (h6 : b6 < 256) :
    (b0 ||| b1 * 2 ^ 8 ||| b2 * 2 ^ 16 ||| b3 * 2 ^ 24 ||| b4 * 2 ^ 32 ||| b5 * 2 ^ 40 |||
      b6 * 2 ^ 48 ||| b7 * 2 ^ 56) =
      b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16 + b3 * 2 ^ 24 + b4 * 2 ^ 32 + b5 * 2 ^ 40 + b6 * 2 ^ 48 +
        b7 * 2 ^ 56 := by
  rw [or_mul_two_pow (x := b0) (by omega),
    or_mul_two_pow (x := b0 + b1 * 2 ^ 8) (by omega),
    or_mul_two_pow (x := b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16) (by omega),
    or_mul_two_pow (x := b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16 + b3 * 2 ^ 24) (by omega),
    or_mul_two_pow (x := b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16 + b3 * 2 ^ 24 + b4 * 2 ^ 32) (by omega),
    or_mul_two_pow (x := b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16 + b3 * 2 ^ 24 + b4 * 2 ^ 32 +
      b5 * 2 ^ 40) (by omega),
    or_mul_two_pow (x := b0 + b1 * 2 ^ 8 + b2 * 2 ^ 16 + b3 * 2 ^ 24 + b4 * 2 ^ 32 +
      b5 * 2 ^ 40 + b6 * 2 ^ 48) (by omega)]

theorem byte_lt (b : UInt8) : b.toNat < 256 := b.toNat_lt

theorem shl_byte (b : UInt8) (k : Nat) (hk : k ≤ 56) :
    (b.toUInt64 <<< UInt64.ofNat k).toNat = b.toNat * 2 ^ k := by
  rw [UInt64.toNat_shiftLeft, UInt8.toNat_toUInt64, Nat.shiftLeft_eq]
  have hk' : (UInt64.ofNat k).toNat % 64 = k := by
    rw [UInt64.toNat_ofNat']; omega
  rw [hk']
  have := byte_lt b
  have h56 : 2 ^ k ≤ 2 ^ 56 := Nat.pow_le_pow_right (by decide) hk
  apply Nat.mod_eq_of_lt
  calc b.toNat * 2 ^ k < 256 * 2 ^ 56 := by
        apply Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos k))
        exact Nat.mul_le_mul_left 256 h56
    _ = 2 ^ 64 := by decide

/-- `load64` is the little-endian sum of its bytes. -/
theorem load64_toNat (m : UInt64 → UInt8) (a : UInt64) :
    (load64 m a).toNat = (m a).toNat + (m (a + 1)).toNat * 2 ^ 8 +
      (m (a + 2)).toNat * 2 ^ 16 + (m (a + 3)).toNat * 2 ^ 24 + (m (a + 4)).toNat * 2 ^ 32 +
      (m (a + 5)).toNat * 2 ^ 40 + (m (a + 6)).toNat * 2 ^ 48 + (m (a + 7)).toNat * 2 ^ 56 := by
  unfold load64
  simp only [UInt64.toNat_or]
  rw [show (8 : UInt64) = UInt64.ofNat 8 from rfl, show (16 : UInt64) = UInt64.ofNat 16 from rfl,
    show (24 : UInt64) = UInt64.ofNat 24 from rfl, show (32 : UInt64) = UInt64.ofNat 32 from rfl,
    show (40 : UInt64) = UInt64.ofNat 40 from rfl, show (48 : UInt64) = UInt64.ofNat 48 from rfl,
    show (56 : UInt64) = UInt64.ofNat 56 from rfl,
    shl_byte _ 8 (by decide), shl_byte _ 16 (by decide), shl_byte _ 24 (by decide),
    shl_byte _ 32 (by decide), shl_byte _ 40 (by decide), shl_byte _ 48 (by decide),
    shl_byte _ 56 (by decide), UInt8.toNat_toUInt64]
  have h0 := byte_lt (m a)
  have h1 := byte_lt (m (a + 1))
  have h2 := byte_lt (m (a + 2))
  have h3 := byte_lt (m (a + 3))
  have h4 := byte_lt (m (a + 4))
  have h5 := byte_lt (m (a + 5))
  have h6 := byte_lt (m (a + 6))
  exact or8 _ h0 h1 h2 h3 h4 h5 h6

/-- The byte at `a + k` of a `store64` at `a`, for `k < 8`. -/
theorem store64_at (m : UInt64 → UInt8) (a v : UInt64) (k : Nat) (hk : k < 8) :
    (store64 m a v (a + UInt64.ofNat k)).toNat = v.toNat / 2 ^ (8 * k) % 256 := by
  have hd : a + UInt64.ofNat k - a = UInt64.ofNat k := by
    rw [UInt64.add_comm, UInt64.add_sub_cancel]
  have hlt : UInt64.ofNat k < 8 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat']; simp; omega
  simp only [store64, hd, hlt, ite_true, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  have : (UInt64.ofNat k * 8).toNat % 64 = 8 * k := by
    rw [UInt64.toNat_mul, UInt64.toNat_ofNat']; simp; omega
  rw [this]

theorem add_ofNat_zero (a : UInt64) : a + UInt64.ofNat 0 = a := by
  simp

/-- A `load64` after a `store64` at the same address reads the stored word. -/
theorem load64_store64_same (m : UInt64 → UInt8) (a v : UInt64) :
    load64 (store64 m a v) a = v := by
  apply UInt64.toNat_inj.mp
  rw [load64_toNat]
  rw [show a + 1 = a + UInt64.ofNat 1 from rfl, show a + 2 = a + UInt64.ofNat 2 from rfl,
    show a + 3 = a + UInt64.ofNat 3 from rfl, show a + 4 = a + UInt64.ofNat 4 from rfl,
    show a + 5 = a + UInt64.ofNat 5 from rfl, show a + 6 = a + UInt64.ofNat 6 from rfl,
    show a + 7 = a + UInt64.ofNat 7 from rfl]
  have e0 := store64_at m a v 0 (by decide)
  rw [add_ofNat_zero] at e0
  rw [e0, store64_at _ _ _ 1 (by decide),
    store64_at _ _ _ 2 (by decide), store64_at _ _ _ 3 (by decide),
    store64_at _ _ _ 4 (by decide), store64_at _ _ _ 5 (by decide),
    store64_at _ _ _ 6 (by decide), store64_at _ _ _ 7 (by decide)]
  have := v.toNat_lt
  omega

/-- A byte that a `store64` at `a` does not cover keeps its value. -/
theorem store64_other (m : UInt64 → UInt8) (a v b : UInt64) (h : ¬ b - a < 8) :
    store64 m a v b = m b := by
  simp [store64, h]

/-- A `load64` of 8 bytes that a `store64` does not cover reads what it read before. -/
theorem load64_store64_other (m : UInt64 → UInt8) (a v b : UInt64)
    (h : ∀ k < 8, ¬ b + UInt64.ofNat k - a < 8) :
    load64 (store64 m a v) b = load64 m b := by
  unfold load64
  rw [store64_other m a v b (by simpa using h 0 (by decide)),
    store64_other m a v (b + 1) (h 1 (by decide)), store64_other m a v (b + 2) (h 2 (by decide)),
    store64_other m a v (b + 3) (h 3 (by decide)), store64_other m a v (b + 4) (h 4 (by decide)),
    store64_other m a v (b + 5) (h 5 (by decide)), store64_other m a v (b + 6) (h 6 (by decide)),
    store64_other m a v (b + 7) (h 7 (by decide))]

/-- A `MOVK` at `sh`, 16, 32, or 48, into a value below `2 ^ sh` adds its field there. -/
theorem movk_add (x : UInt64) (imm sh : Nat) (hx : x.toNat < 2 ^ sh) (him : imm < 65536)
    (hsh : sh = 16 ∨ sh = 32 ∨ sh = 48) :
    ((x &&& ~~~((0xFFFF : UInt64) <<< UInt64.ofNat sh)) |||
      UInt64.ofNat imm <<< UInt64.ofNat sh).toNat = x.toNat + imm * 2 ^ sh := by
  have hsh' : (UInt64.ofNat sh).toNat % 64 = sh := by
    rw [UInt64.toNat_ofNat']; rcases hsh with rfl | rfl | rfl <;> decide
  have hpow : 2 ^ sh ≤ 2 ^ 48 := Nat.pow_le_pow_right (by decide) (by omega)
  have hmask : (0xFFFF : UInt64).toNat * 2 ^ sh % 2 ^ 64 = 65535 * 2 ^ sh := by
    rw [show (0xFFFF : UInt64).toNat = 65535 from rfl]
    apply Nat.mod_eq_of_lt
    calc 65535 * 2 ^ sh ≤ 65535 * 2 ^ 48 := Nat.mul_le_mul_left _ hpow
      _ < 2 ^ 64 := by decide
  have himm : (UInt64.ofNat imm).toNat * 2 ^ sh % 2 ^ 64 = imm * 2 ^ sh := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (show imm < 2 ^ 64 by omega)]
    apply Nat.mod_eq_of_lt
    calc imm * 2 ^ sh < 65536 * 2 ^ sh := Nat.mul_lt_mul_of_pos_right him (Nat.two_pow_pos sh)
      _ ≤ 65536 * 2 ^ 48 := Nat.mul_le_mul_left _ hpow
      _ = 2 ^ 64 := by decide
  simp only [UInt64.toNat_or, UInt64.toNat_and, UInt64.toNat_not, UInt64.toNat_shiftLeft,
    Nat.shiftLeft_eq, hsh', hmask, himm]
  have hand : x.toNat &&& (UInt64.size - 1 - 65535 * 2 ^ sh) = x.toNat := by
    have hle : x.toNat &&& (UInt64.size - 1 - 65535 * 2 ^ sh) < 2 ^ sh :=
      Nat.lt_of_le_of_lt Nat.and_le_left hx
    rw [← Nat.mod_eq_of_lt hle, Nat.and_mod_two_pow, Nat.mod_eq_of_lt hx]
    have hlow : (UInt64.size - 1 - 65535 * 2 ^ sh) % 2 ^ sh = 2 ^ sh - 1 := by
      rcases hsh with rfl | rfl | rfl <;> decide
    rw [hlow, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt hx]
  rw [hand, or_mul_two_pow hx]

end LeanExe.A64
