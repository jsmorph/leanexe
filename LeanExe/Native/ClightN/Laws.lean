import LeanExe.Native.ClightN.Spec

/-!
The laws of the base symbols of `clightn/N.nsx`, proved of the definitions in `Base.lean`.  Rocq
proves the same statements of the definitions in `clightn/rocq/NBase.v`.
-/

namespace ClightN.Proof

open ClightN.Base ClightN.Spec

theorem modulus32 : LClight.Int.modulus = 4294967296 := rfl
theorem modulus64 : LClight.Int64.modulus = 18446744073709551616 := rfl
theorem half64 : LClight.Int64.half_modulus = 9223372036854775808 := rfl

theorem u32_range : stmt_u32_range := by
  intro x
  have := x.toNat_lt
  simp only [u32, LClight.Int.unsigned, Nat.reducePow] at *
  omega

theorem u32_r32 : stmt_u32_r32 := by
  intro z
  have h0 : 0 ≤ z % 4294967296 := Int.emod_nonneg _ (by decide)
  have h1 : z % 4294967296 < 4294967296 := Int.emod_lt_of_pos _ (by decide)
  simp only [u32, r32, zmod, LClight.Int.unsigned, LClight.Int.repr, modulus32,
    UInt32.toNat_ofNat', Nat.reducePow]
  omega

theorem r32_u32 : stmt_r32_u32 := by
  intro x
  have := x.toNat_lt
  simp only [Nat.reducePow] at this
  have h : ((x.toNat : Int) % 4294967296).toNat = x.toNat := by omega
  simp only [r32, u32, LClight.Int.repr, LClight.Int.unsigned, modulus32, h, UInt32.ofNat_toNat]

theorem u64_range : stmt_u64_range := by
  intro x
  have := x.toNat_lt
  simp only [u64, LClight.Int64.unsigned, Nat.reducePow] at *
  omega

theorem u64_r64 : stmt_u64_r64 := by
  intro z
  have h0 : 0 ≤ z % 18446744073709551616 := Int.emod_nonneg _ (by decide)
  have h1 : z % 18446744073709551616 < 18446744073709551616 := Int.emod_lt_of_pos _ (by decide)
  simp only [u64, r64, zmod, LClight.Int64.unsigned, LClight.Int64.repr, modulus64,
    UInt64.toNat_ofNat', Nat.reducePow]
  omega

theorem r64_u64 : stmt_r64_u64 := by
  intro x
  have := x.toNat_lt
  simp only [Nat.reducePow] at this
  have h : ((x.toNat : Int) % 18446744073709551616).toNat = x.toNat := by omega
  simp only [r64, u64, LClight.Int64.repr, LClight.Int64.unsigned, modulus64, h,
    UInt64.ofNat_toNat]

theorem s64_low : stmt_s64_low := by
  intro x h
  simp only [s64, u64, LClight.Int64.signed] at h ⊢
  split
  · rfl
  · rename_i hn
    rw [half64] at hn
    omega

theorem s64_high : stmt_s64_high := by
  intro x h
  simp only [s64, u64, LClight.Int64.signed] at h ⊢
  split
  · rename_i hn
    rw [half64] at hn
    omega
  · rw [modulus64]

theorem zdiv_zmod : stmt_zdiv_zmod := by
  intro a b hb
  have h := Int.emod_add_ediv_mul a b
  have := Int.emod_nonneg a (b := b) (by omega)
  have := Int.emod_lt_of_pos a hb
  simp only [zdiv, zmod]
  rw [Int.mul_comm]
  omega

theorem pow2_zero : stmt_pow2_zero := rfl

theorem pow2_succ : stmt_pow2_succ := by
  intro k hk
  simp only [pow2]
  rw [show (k + 1).toNat = k.toNat + 1 by omega, Int.pow_succ, Int.mul_comm]

/-- Bit `k` of a natural number, as the specification writes it. -/
theorem bit_nat (n : Nat) (k : Int) :
    zmod (zdiv (n : Int) (pow2 k)) 2 = ((n / 2 ^ k.toNat % 2 : Nat) : Int) := rfl

/-- The bits of `A` and `B` at `j` and the bit `C` of their combination by `op`, each 0 or 1,
satisfy `f` when the bits as Booleans satisfy `g`. -/
theorem bit_cases (A B C j : Nat) (g : Bool → Bool → Bool) (f : Nat → Nat → Nat → Prop)
    (hg : C.testBit j = g (A.testBit j) (B.testBit j))
    (hf : ∀ x y : Bool, f x.toNat y.toNat (g x y).toNat) :
    f (A / 2 ^ j % 2) (B / 2 ^ j % 2) (C / 2 ^ j % 2) := by
  have bit (n : Nat) : n / 2 ^ j % 2 = (n.testBit j).toNat := by
    rw [Nat.testBit_eq_decide_div_mod_eq]
    rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ j) with h | h <;> simp [h]
  rw [bit A, bit B, bit C, hg]
  exact hf _ _

theorem land_bits : stmt_land_bits := by
  intro a b k ha hb _
  obtain ⟨A, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨B, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  show zmod (zdiv ((A &&& B : Nat) : Int) (pow2 k)) 2 = _
  rw [bit_nat, bit_nat, bit_nat, ← Int.natCast_mul]
  have := bit_cases A B (A &&& B) k.toNat (· && ·) (fun x y z => z = x * y)
    (Nat.testBit_and A B k.toNat) (by intro x y; cases x <;> cases y <;> rfl)
  omega

theorem land_nonneg : stmt_land_nonneg := by
  intro a b _ _
  exact Int.natCast_nonneg _

theorem lor_bits : stmt_lor_bits := by
  intro a b k ha hb _
  obtain ⟨A, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨B, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  show zmod (zdiv ((A ||| B : Nat) : Int) (pow2 k)) 2 = _
  rw [bit_nat, bit_nat, bit_nat, ← Int.natCast_mul]
  have := bit_cases A B (A ||| B) k.toNat (· || ·) (fun x y z => z + x * y = x + y)
    (Nat.testBit_or A B k.toNat) (by intro x y; cases x <;> cases y <;> rfl)
  omega

theorem lor_nonneg : stmt_lor_nonneg := by
  intro a b _ _
  exact Int.natCast_nonneg _

theorem lxor_bits : stmt_lxor_bits := by
  intro a b k ha hb _
  obtain ⟨A, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  obtain ⟨B, rfl⟩ := Int.eq_ofNat_of_zero_le hb
  show zmod (zdiv ((A ^^^ B : Nat) : Int) (pow2 k)) 2 = _
  rw [bit_nat, bit_nat, bit_nat]
  have := bit_cases A B (A ^^^ B) k.toNat (fun x y => x ^^ y) (fun x y z => z = (x + y) % 2)
    (Nat.testBit_xor A B k.toNat) (by intro x y; cases x <;> cases y <;> rfl)
  simp only [zmod]
  omega

theorem lxor_nonneg : stmt_lxor_nonneg := by
  intro a b _ _
  exact Int.natCast_nonneg _

end ClightN.Proof
