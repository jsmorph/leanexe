import LeanExe.M7.Machine

/-!
Values of 64-bit numbers in pairs of 32-bit words, and the results of the instruction sequences
that compute on pairs, stated over natural numbers.  `pairNat lo hi` is `hi · 2^32 + lo`, the number
whose low word is `lo` and whose high word is `hi`.  Each lemma about a sequence takes the words
that the model's `exec` writes, in the terms of `addWithCarry`, `shl`, `shr`, and `clz32`, and
gives the number of the result: `SUBS` and `SBCS` subtract with a borrow, `ADDS` and `ADC` add with
a carry, `LSL`, `LSR`, and `ORR` by a register amount below 64 shift a pair left as CompCert's
`LSHL` does, and `CLZ`, `LSR`, and `MLA` count the leading zero bits of a pair.  The proofs convert
words to natural numbers and decide linear goals with `omega`.  `grind` proves the identities of
products whose factors include a power of 2 with a variable exponent, which `omega` treats as
unknown terms.
-/

namespace LeanExe.M7

/-! ## Words -/

theorem toNat_lt32 (x : UInt32) : x.toNat < 4294967296 := x.toNat_lt_size

theorem toNat_addWithCarry (x y : UInt32) (c : Bool) :
    (addWithCarry x y c).1.toNat = (x.toNat + y.toNat + c.toNat) % 4294967296 := by
  simp [addWithCarry]

/-- The carry of `AddWithCarry` is the bit above the low 32 bits of the sum. -/
theorem toNat_carry (x y : UInt32) (c : Bool) :
    (addWithCarry x y c).2.1.toNat = (x.toNat + y.toNat + c.toNat) / 4294967296 := by
  have hx := toNat_lt32 x
  have hy := toNat_lt32 y
  have hc := Bool.toNat_le c
  simp only [addWithCarry, UInt32.toNat_ofNat', Nat.reducePow]
  by_cases h : 4294967296 ≤ x.toNat + y.toNat + c.toNat
  · have hne : (x.toNat + y.toNat + c.toNat) % 4294967296 ≠ x.toNat + y.toNat + c.toNat := by
      omega
    simp only [bne_iff_ne.mpr hne, Bool.toNat_true]
    omega
  · have heq : (x.toNat + y.toNat + c.toNat) % 4294967296 = x.toNat + y.toNat + c.toNat := by
      omega
    simp only [heq, bne_self_eq_false, Bool.toNat_false]
    omega

theorem eq_true_of_toNat {b : Bool} (h : b.toNat = 1) : b = true := by
  cases b <;> simp_all

theorem eq_false_of_toNat {b : Bool} (h : b.toNat = 0) : b = false := by
  cases b <;> simp_all

theorem toNat_not32 (x : UInt32) : (~~~x).toNat = 4294967295 - x.toNat := by
  simp [UInt32.toNat_not, UInt32.size]

/-- `SUB` gives the difference modulo 2^32. -/
theorem sub_addWithCarry (x y : UInt32) : (addWithCarry x (~~~y) true).1 = x - y := by
  apply UInt32.toNat_inj.mp
  rw [toNat_addWithCarry, toNat_not32, UInt32.toNat_sub]
  have := toNat_lt32 y
  simp only [Bool.toNat_true, Nat.reducePow]
  omega

/-- `ADD` without a carry gives the sum modulo 2^32. -/
theorem add_addWithCarry (x y : UInt32) : (addWithCarry x y false).1 = x + y := by
  apply UInt32.toNat_inj.mp
  rw [toNat_addWithCarry, UInt32.toNat_add]
  simp

theorem toNat_shl (x : UInt32) (k : Nat) : (shl x k).toNat = x.toNat * 2 ^ k % 4294967296 := by
  unfold shl
  split
  · rename_i hk
    rw [UInt32.toNat_shiftLeft, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega),
      Nat.mod_eq_of_lt (show k < 32 from hk), Nat.shiftLeft_eq]
  · rename_i hk
    rw [show 2 ^ k = 4294967296 * 2 ^ (k - 32) by
      rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, ← Nat.pow_add]; congr 1; omega]
    rw [Nat.mul_left_comm, Nat.mul_mod_right]
    rfl

theorem toNat_shr (x : UInt32) (k : Nat) : (shr x k).toNat = x.toNat / 2 ^ k := by
  unfold shr
  split
  · rename_i hk
    rw [UInt32.toNat_shiftRight, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega),
      Nat.mod_eq_of_lt (show k < 32 from hk), Nat.shiftRight_eq_div_pow]
  · rename_i hk
    rw [Nat.div_eq_of_lt]
    · rfl
    · calc x.toNat < 2 ^ 32 := toNat_lt32 x
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)

/-- `UDIV` followed by `MLS` gives the remainder. -/
theorem sub_div_mul (x y : UInt32) : x - x / y * y = x % y := by
  apply UInt32.toNat_inj.mp
  have hx := toNat_lt32 x
  have hd := Nat.div_add_mod' x.toNat y.toNat
  have hm : x.toNat % y.toNat ≤ x.toNat := Nat.mod_le _ _
  rw [UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_div, UInt32.toNat_mod]
  generalize x.toNat / y.toNat * y.toNat = p at *
  generalize x.toNat % y.toNat = r at *
  simp only [Nat.reducePow]
  omega

theorem shl_zero (x : UInt32) : shl x 0 = x := by
  apply UInt32.toNat_inj.mp
  rw [toNat_shl, Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt (toNat_lt32 x)]

/-- `CMP` with 0 compares the word itself with 0. -/
theorem cmp_zero (x : UInt32) : (addWithCarry x (~~~(UInt32.ofNat 0)) true).1 = x := by
  apply UInt32.toNat_inj.mp
  rw [toNat_addWithCarry, toNat_not32]
  have := toNat_lt32 x
  simp only [UInt32.toNat_ofNat', Nat.reducePow, Nat.zero_mod, Bool.toNat_true]
  omega

/-! The immediates of `CMP`, `SUB`, and `MOV` as `exec` writes them, from a `Fin 256` field. -/

theorem cmp_imm0 (x : UInt32) : (addWithCarry x (~~~(UInt32.ofNat (0 : Fin 256).val)) true).1 = x :=
  cmp_zero x

theorem sub_imm (x : UInt32) (imm : Fin 256) :
    (addWithCarry x (~~~(UInt32.ofNat imm.val)) true).1 = x - UInt32.ofNat imm.val :=
  sub_addWithCarry _ _

theorem ofNat_imm0 : UInt32.ofNat (0 : Fin 256).val = 0 := rfl

theorem ofNat_imm1 : UInt32.ofNat (1 : Fin 256).val = 1 := rfl

theorem ofNat_imm32 : UInt32.ofNat (32 : Fin 256).val = 32 := rfl

theorem clz32_zero : clz32 0 = 32 := rfl

/-- A nonzero word lies between the powers of 2 that its leading zero count gives. -/
theorem clz32_bounds {x : UInt32} (hx : x ≠ 0) :
    (clz32 x).toNat ≤ 31 ∧ 2 ^ (31 - (clz32 x).toNat) ≤ x.toNat ∧
      x.toNat < 2 ^ (32 - (clz32 x).toNat) := by
  have hx0 : x.toNat ≠ 0 := fun h => hx (UInt32.toNat_inj.mp h)
  have hl : x.toNat.log2 < 32 := (Nat.log2_lt hx0).mpr (toNat_lt32 x)
  have hc : (clz32 x).toNat = 31 - x.toNat.log2 := by
    simp only [clz32, hx, ↓reduceIte, UInt32.toNat_ofNat', Nat.reducePow]
    omega
  rw [hc, show 31 - (31 - x.toNat.log2) = x.toNat.log2 by omega,
    show 32 - (31 - x.toNat.log2) = x.toNat.log2 + 1 by omega]
  exact ⟨by omega, Nat.log2_self_le hx0, Nat.lt_log2_self⟩

theorem clz32_le (x : UInt32) : (clz32 x).toNat ≤ 32 := by
  by_cases hx : x = 0
  · subst hx; decide
  · have := (clz32_bounds hx).1; omega

/-! ## Pairs -/

/-- The number of the pair of words `lo` and `hi`: `hi · 2^32 + lo`. -/
def pairNat (lo hi : UInt32) : Nat := hi.toNat * 4294967296 + lo.toNat

theorem pairNat_lt (lo hi : UInt32) : pairNat lo hi < 18446744073709551616 := by
  have := toNat_lt32 lo
  have := toNat_lt32 hi
  unfold pairNat
  omega

theorem toNat_hi64 (x : UInt64) :
    (x >>> 32).toUInt32.toNat = x.toNat / 4294967296 % 4294967296 := by
  rw [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  rfl

/-- A `UInt64` is the number of its low word and its high word. -/
theorem pairNat_toUInt32 (x : UInt64) : pairNat x.toUInt32 (x >>> 32).toUInt32 = x.toNat := by
  have : x.toNat < 18446744073709551616 := x.toNat_lt_size
  rw [pairNat, toNat_hi64, UInt64.toNat_toUInt32]
  simp only [Nat.reducePow]
  omega

/-- The words of a pair whose number is that of a `UInt64` are the `UInt64`'s low and high words. -/
theorem eq_of_pairNat {lo hi : UInt32} {x : UInt64} (h : pairNat lo hi = x.toNat) :
    lo = x.toUInt32 ∧ hi = (x >>> 32).toUInt32 := by
  have := toNat_lt32 lo
  have := toNat_lt32 hi
  unfold pairNat at h
  constructor <;> apply UInt32.toNat_inj.mp
  · rw [UInt64.toNat_toUInt32]; simp only [Nat.reducePow]; omega
  · rw [toNat_hi64]; omega

/-- `SUBS` of the low words and `SBCS` of the high words give the difference modulo 2^64, and the
carry that `SBCS` leaves is set when the subtraction does not borrow. -/
theorem sub_pair (a0 a1 b0 b1 : UInt32) :
    pairNat (addWithCarry a0 (~~~b0) true).1
        (addWithCarry a1 (~~~b1) (addWithCarry a0 (~~~b0) true).2.1).1 =
      (pairNat a0 a1 + 18446744073709551616 - pairNat b0 b1) % 18446744073709551616 ∧
    ((addWithCarry a1 (~~~b1) (addWithCarry a0 (~~~b0) true).2.1).2.1 = true ↔
      pairNat b0 b1 ≤ pairNat a0 a1) := by
  have := toNat_lt32 a0
  have := toNat_lt32 a1
  have := toNat_lt32 b0
  have := toNat_lt32 b1
  have e0 := toNat_carry a0 (~~~b0) true
  have e1 := toNat_carry a1 (~~~b1) (addWithCarry a0 (~~~b0) true).2.1
  simp only [pairNat, toNat_addWithCarry, toNat_not32, Bool.toNat_true] at e0 e1 ⊢
  generalize (addWithCarry a0 (~~~b0) true).2.1 = c0 at *
  generalize (addWithCarry a1 (~~~b1) c0).2.1 = c1 at *
  have := Bool.toNat_le c0
  constructor
  · omega
  · cases c1 <;> simp only [Bool.toNat_true, Bool.toNat_false, Bool.false_eq_true,
      false_iff, true_iff, Nat.not_le] at e1 ⊢ <;> omega

/-- `ADDS` of the low words and `ADC` of the high words give the sum modulo 2^64. -/
theorem add_pair (a0 a1 b0 b1 : UInt32) :
    pairNat (addWithCarry a0 b0 false).1 (addWithCarry a1 b1 (addWithCarry a0 b0 false).2.1).1 =
      (pairNat a0 a1 + pairNat b0 b1) % 18446744073709551616 := by
  have := toNat_lt32 a0
  have := toNat_lt32 a1
  have := toNat_lt32 b0
  have := toNat_lt32 b1
  simp only [pairNat, toNat_addWithCarry, toNat_carry, Bool.toNat_false]
  omega

/-- `LSR #1` of the low word, `ADD` of the high word `LSL #31`, and `LSR #1` of the high word halve
a pair. -/
theorem half_pair (lo hi : UInt32) :
    pairNat (addWithCarry (shr lo 1) (shl hi 31) false).1 (shr hi 1) = pairNat lo hi / 2 := by
  have := toNat_lt32 lo
  have := toNat_lt32 hi
  simp only [pairNat, toNat_addWithCarry, toNat_shl, toNat_shr, Bool.toNat_false, Nat.reducePow]
  omega

/-- `LSR #31` of the low word, `ADD` of it and the high word `LSL #1`, and `ADC` of the low word to
itself double a pair and add the carry `c`, modulo 2^64. -/
theorem double_pair (lo hi : UInt32) (c : Bool) :
    pairNat (addWithCarry lo lo c).1 (addWithCarry (shr lo 31) (shl hi 1) false).1 =
      (2 * pairNat lo hi + c.toNat) % 18446744073709551616 := by
  have := toNat_lt32 lo
  have := toNat_lt32 hi
  have := Bool.toNat_le c
  simp only [pairNat, toNat_addWithCarry, toNat_shl, toNat_shr, Bool.toNat_false, Nat.reducePow]
  omega

/-! ## Leading zeros -/

/-- The leading zero count of a pair as `CLZ` of each word, `LSR #5` of the high word's count, and
`MLA` give it: the high word's count, plus the low word's when the high word is 0, whose count of
32 is the only one that `LSR #5` takes to 1. -/
def clzPair (lo hi : UInt32) : UInt32 := clz32 hi + clz32 lo * shr (clz32 hi) 5

/-- A pair with a nonzero high word lies between the powers of 2 that the high word's leading zero
count gives. -/
theorem pair_bounds_of_hi {lo hi : UInt32} (h : hi ≠ 0) :
    2 ^ (63 - (clz32 hi).toNat) ≤ pairNat lo hi ∧
      pairNat lo hi < 2 ^ (64 - (clz32 hi).toNat) := by
  obtain ⟨hc, h1, h2⟩ := clz32_bounds h
  have hlo := toNat_lt32 lo
  generalize (clz32 hi).toNat = c at *
  have e1 : 2 ^ (63 - c) = 2 ^ (31 - c) * 4294967296 := by
    rw [show 63 - c = (31 - c) + 32 by omega, Nat.pow_add]
  have e2 : 2 ^ (64 - c) = 2 ^ (32 - c) * 4294967296 := by
    rw [show 64 - c = (32 - c) + 32 by omega, Nat.pow_add]
  unfold pairNat
  rw [e1, e2]
  constructor
  · exact Nat.le_trans (Nat.mul_le_mul_right _ h1) (Nat.le_add_right _ _)
  · calc hi.toNat * 4294967296 + lo.toNat < (hi.toNat + 1) * 4294967296 := by omega
      _ ≤ 2 ^ (32 - c) * 4294967296 := Nat.mul_le_mul_right _ h2

/-- A nonzero pair lies between the powers of 2 that its leading zero count gives. -/
theorem clzPair_bounds {lo hi : UInt32} (h : pairNat lo hi ≠ 0) :
    (clzPair lo hi).toNat ≤ 63 ∧ 2 ^ (63 - (clzPair lo hi).toNat) ≤ pairNat lo hi ∧
      pairNat lo hi < 2 ^ (64 - (clzPair lo hi).toNat) := by
  have hl := clz32_le lo
  by_cases hhi : hi = 0
  · subst hhi
    have hlo : lo ≠ 0 := by rintro rfl; exact h rfl
    obtain ⟨hc, h1, h2⟩ := clz32_bounds hlo
    have e : (clzPair lo 0).toNat = 32 + (clz32 lo).toNat := by
      unfold clzPair
      rw [clz32_zero, UInt32.toNat_add, UInt32.toNat_mul, toNat_shr]
      simp only [show (32 : UInt32).toNat = 32 from rfl, Nat.reducePow, Nat.reduceDiv,
        Nat.mul_one]
      omega
    have hp : pairNat lo 0 = lo.toNat := by simp [pairNat]
    rw [e, hp]
    refine ⟨by omega, ?_, ?_⟩
    · rw [show 63 - (32 + (clz32 lo).toNat) = 31 - (clz32 lo).toNat by omega]; exact h1
    · rw [show 64 - (32 + (clz32 lo).toNat) = 32 - (clz32 lo).toNat by omega]; exact h2
  · have hc := (clz32_bounds hhi).1
    have e : (clzPair lo hi).toNat = (clz32 hi).toNat := by
      unfold clzPair
      rw [UInt32.toNat_add, UInt32.toNat_mul, toNat_shr,
        show (clz32 hi).toNat / 2 ^ 5 = 0 by simp only [Nat.reducePow]; omega, Nat.mul_zero]
      simp only [Nat.zero_mod, Nat.add_zero, Nat.reducePow]
      exact Nat.mod_eq_of_lt (toNat_lt32 _)
    rw [e]
    exact ⟨by omega, pair_bounds_of_hi hhi⟩

/-! ## Shifts by a register amount -/

/-- The high word of a pair shifted left by `k`, as `LSL`, `LSR`, and `ORR` compute it with the
amounts `k`, `32 - k`, and `k - 32`, of which a register shift takes the bottom byte. -/
def shlHigh (lo hi k : UInt32) : UInt32 :=
  shl hi (k.toNat % 256) ||| shr lo ((32 - k).toNat % 256) ||| shl lo ((k - 32).toNat % 256)

theorem or_of_lt {a b : Nat} (k : Nat) (hb : b < 2 ^ k) : a * 2 ^ k ||| b = a * 2 ^ k + b := by
  rw [Nat.mul_comm]
  exact (Nat.two_pow_add_eq_or_of_lt hb a).symm

/-- A word times `2^n`, for `n + j = 32`, split at bit 32: the bits from bit `j` up move above bit
32. -/
theorem mul_pow_split (x n j : Nat) (hnj : n + j = 32) :
    x * 2 ^ n = x / 2 ^ j * 4294967296 + x % 2 ^ j * 2 ^ n := by
  have h := Nat.div_add_mod x (2 ^ j)
  have hp : 2 ^ j * 2 ^ n = 4294967296 := by
    rw [← Nat.pow_add, show j + n = 32 by omega]
  grind

theorem shl_pair_low {H L n : Nat} (hL : L < 4294967296) (hn : n < 32) :
    (H * 2 ^ n % 4294967296 ||| L / 2 ^ (32 - n)) * 4294967296 + L * 2 ^ n % 4294967296 =
      (H * 4294967296 + L) * 2 ^ n % 18446744073709551616 := by
  have hQ : 0 < 2 ^ (32 - n) := Nat.two_pow_pos _
  have hPQ : 2 ^ (32 - n) * 2 ^ n = 4294967296 := by
    rw [← Nat.pow_add, show 32 - n + n = 32 by omega]
  have sH := mul_pow_split H n (32 - n) (by omega)
  have sL := mul_pow_split L n (32 - n) (by omega)
  have hc : L / 2 ^ (32 - n) < 2 ^ n :=
    (Nat.div_lt_iff_lt_mul hQ).mpr (by rw [Nat.mul_comm, hPQ]; exact hL)
  have hb : (H % 2 ^ (32 - n) + 1) * 2 ^ n ≤ 4294967296 := by
    rw [← hPQ]; exact Nat.mul_le_mul_right _ (Nat.mod_lt _ hQ)
  have he : (L % 2 ^ (32 - n) + 1) * 2 ^ n ≤ 4294967296 := by
    rw [← hPQ]; exact Nat.mul_le_mul_right _ (Nat.mod_lt _ hQ)
  have hm : (H * 4294967296 + L) * 2 ^ n = H * 2 ^ n * 4294967296 + L * 2 ^ n := by grind
  have hP : 0 < 2 ^ n := Nat.two_pow_pos n
  rw [Nat.add_mul, Nat.one_mul] at hb he
  have hX : H * 2 ^ n % 4294967296 = H % 2 ^ (32 - n) * 2 ^ n := by
    rw [sH, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  have hY : L * 2 ^ n % 4294967296 = L % 2 ^ (32 - n) * 2 ^ n := by
    rw [sL, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  rw [hX, hY, or_of_lt n hc, hm, sH, sL]
  generalize H / 2 ^ (32 - n) = a at *
  generalize H % 2 ^ (32 - n) * 2 ^ n = X at *
  generalize L / 2 ^ (32 - n) = c at *
  generalize L % 2 ^ (32 - n) * 2 ^ n = Y at *
  generalize 2 ^ n = P at *
  clear sH sL hm hPQ hQ hX hY
  omega

theorem shl_pair_high {H L n : Nat} (hL : L < 4294967296) (hn1 : 32 ≤ n) (hn2 : n < 64) :
    (L / 2 ^ ((4294967328 - n) % 4294967296 % 256) |||
        L * 2 ^ ((4294967264 + n) % 4294967296 % 256) % 4294967296) * 4294967296 =
      (H * 4294967296 + L) * 2 ^ n % 18446744073709551616 := by
  rw [show (4294967264 + n) % 4294967296 % 256 = n - 32 by omega]
  have hs : 2 ^ n = 4294967296 * 2 ^ (n - 32) := by
    rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, ← Nat.pow_add, show 32 + (n - 32) = n by omega]
  have hm : (H * 4294967296 + L) * 2 ^ n =
      H * 2 ^ (n - 32) * 18446744073709551616 + L * 2 ^ (n - 32) * 4294967296 := by
    rw [hs]; grind
  have hmid : L / 2 ^ ((4294967328 - n) % 4294967296 % 256) |||
      L * 2 ^ (n - 32) % 4294967296 = L * 2 ^ (n - 32) % 4294967296 := by
    by_cases h32 : n = 32
    · subst h32
      rw [show (4294967328 - 32) % 4294967296 % 256 = 0 from rfl, show 32 - 32 = 0 from rfl,
        Nat.pow_zero, Nat.div_one, Nat.mul_one, Nat.mod_eq_of_lt hL, Nat.or_self]
    · have hle : (4294967296 : Nat) ≤ 2 ^ ((4294967328 - n) % 4294967296 % 256) :=
        Nat.pow_le_pow_right (n := 2) (i := 32) (by decide) (by omega)
      have hlt : L < 2 ^ ((4294967328 - n) % 4294967296 % 256) := Nat.lt_of_lt_of_le hL hle
      rw [Nat.div_eq_of_lt hlt, Nat.zero_or]
  rw [hmid, hm]
  generalize L * 2 ^ (n - 32) = Z
  generalize H * 2 ^ (n - 32) = W
  omega

/-- A pair shifted left by an amount below 64. -/
theorem shl_pair (lo hi k : UInt32) (hk : k.toNat < 64) :
    pairNat (shl lo (k.toNat % 256)) (shlHigh lo hi k) =
      pairNat lo hi * 2 ^ k.toNat % 18446744073709551616 := by
  have hlo := toNat_lt32 lo
  have hhi := toNat_lt32 hi
  have hk' := toNat_lt32 k
  have e32 : (32 : UInt32).toNat = 32 := rfl
  have h32 : (32 - k).toNat % 256 = (4294967328 - k.toNat) % 4294967296 % 256 := by
    rw [UInt32.toNat_sub, e32] <;> simp only [Nat.reducePow] <;> omega
  have hk32 : (k - 32).toNat % 256 = (4294967264 + k.toNat) % 4294967296 % 256 := by
    rw [UInt32.toNat_sub, e32] <;> simp only [Nat.reducePow] <;> omega
  unfold shlHigh pairNat
  rw [h32, hk32, Nat.mod_eq_of_lt (show k.toNat < 256 by omega), UInt32.toNat_or,
    UInt32.toNat_or, toNat_shl, toNat_shl, toNat_shl, toNat_shr]
  generalize k.toNat = n at *
  generalize lo.toNat = L at *
  generalize hi.toNat = H at *
  by_cases hn : n < 32
  · have hz : L * 2 ^ ((4294967264 + n) % 4294967296 % 256) % 4294967296 = 0 := by
      rw [show (4294967264 + n) % 4294967296 % 256 = 32 + (192 + n) by omega, Nat.pow_add,
        show (2 : Nat) ^ 32 = 4294967296 from rfl, Nat.mul_left_comm, Nat.mul_mod_right]
    rw [show (4294967328 - n) % 4294967296 % 256 = 32 - n by omega, hz, Nat.or_zero]
    exact shl_pair_low hlo hn
  · have hs : 2 ^ n = 4294967296 * 2 ^ (n - 32) := by
      rw [show (4294967296 : Nat) = 2 ^ 32 from rfl, ← Nat.pow_add,
        show 32 + (n - 32) = n by omega]
    have hhi0 : H * 2 ^ n % 4294967296 = 0 := by rw [hs, Nat.mul_left_comm, Nat.mul_mod_right]
    have hlo0 : L * 2 ^ n % 4294967296 = 0 := by rw [hs, Nat.mul_left_comm, Nat.mul_mod_right]
    rw [hhi0, hlo0, Nat.zero_or, Nat.add_zero]
    exact shl_pair_high hlo (by omega) hk

end LeanExe.M7
