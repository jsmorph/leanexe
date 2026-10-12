import Verified.Examples.SinpiReflect

/-!
The words of `Sinpi`: `ax` built from the high and low words of `x` is `|x|`, the flag `neg` is the
sign bit, and `Sinpi.ffloor` clears the fraction bits of `|x|` below its units bit, which leaves
the integer part of `|x|` for `1 ≤ |x| < 2 ^ 52`.
-/

namespace Verified.Examples.SinpiBits

open CodeLib.IEEE64 LeanExe.ProofKit TrigSinCos TanBigWords TanStep

/-- Clearing the low `m` bits of a number below `2 ^ k` with the mask `(2 ^ (k - m) - 1) 2 ^ m`. -/
theorem land_clear (n m k : Nat) (hm : m ≤ k) (hn : n < 2 ^ k) :
    n &&& ((2 ^ (k - m) - 1) * 2 ^ m) = n / 2 ^ m * 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_mul_two_pow,
    Nat.testBit_two_pow_sub_one, Nat.testBit_div_two_pow]
  by_cases h1 : m ≤ i
  · have : i - m + m = i := by omega
    rw [this]
    by_cases h2 : i < k
    · simp [h1, show i - m < k - m by omega]
    · have : n.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
      simp [h1, this, show ¬ i - m < k - m by omega]
  · simp [h1]

theorem low_ones (n j : Nat) (hj : j ≤ n) : (2 ^ n - 1) / 2 ^ j = 2 ^ (n - j) - 1 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  simp only [decide_eq_decide]
  omega

theorem xor_mask (m : Nat) (hm : m ≤ 32) :
    (2 ^ 32 - 1) ^^^ (2 ^ m - 1) = (2 ^ (32 - m) - 1) * 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one]
  by_cases h1 : m ≤ i
  · by_cases h2 : i < 32
    · simp [h1, h2, show ¬ i < m by omega, show i - m < 32 - m by omega]
    · simp [h1, h2, show ¬ i < m by omega, show ¬ i - m < 32 - m by omega]
  · simp [h1, show i < 32 by omega, show i < m by omega]

theorem ax_toNat (b : UInt64) :
    ((((b >>> 32) &&& 0x7fffffff) <<< 32) ||| (b &&& 0xFFFFFFFF)).toNat = b.toNat % 2 ^ 63 := by
  have hb := b.toNat_lt
  have hix := TrigSinCos.high_word b
  have hlx : (b &&& 0xFFFFFFFF).toNat = b.toNat % 2 ^ 32 := by
    rw [UInt64.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod _ 32
  have hsh : (((b >>> 32) &&& 0x7fffffff) <<< 32).toNat = b.toNat % 2 ^ 63 / 2 ^ 32 * 2 ^ 32 := by
    rw [TrigWords.shl_toNat, hix, show (32 : UInt64).toNat % 64 = 32 from rfl]
    apply Nat.mod_eq_of_lt
    omega
  rw [UInt64.toNat_or, hsh, hlx, Nat.mul_comm (b.toNat % 2 ^ 63 / 2 ^ 32) (2 ^ 32),
    ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by positivity))]
  omega

/-- `ax` is `|x|`. -/
theorem ax_abs (x : Float) :
    Float.ofBits ((((x.toBits >>> 32) &&& 0x7fffffff) <<< 32) ||| (x.toBits &&& 0xFFFFFFFF)) =
      x.abs := by
  have h : (((x.toBits >>> 32) &&& 0x7fffffff) <<< 32) ||| (x.toBits &&& 0xFFFFFFFF) =
      Wasm.IEEE64.abs x.toBits :=
    UInt64.toNat_inj.mp (by rw [ax_toNat, abs_toNat])
  rw [h, ← F64Bits.toBits_abs, F64Bits.ofBits_toBits]

/-- The flag `neg` is the sign bit. -/
theorem neg_flag (b : UInt64) : ((b >>> 32 &&& 0x80000000) != 0) = Wasm.IEEE64.sign b := by
  have hb := b.toNat_lt
  have h1 : (b >>> 32 &&& 0x80000000).toNat = b.toNat / 2 ^ 32 / 2 ^ 31 * 2 ^ 31 := by
    rw [UInt64.toNat_and, TrigWords.shr_toNat, show (32 : UInt64).toNat % 64 = 32 from rfl,
      show (0x80000000 : UInt64).toNat = (2 ^ (32 - 31) - 1) * 2 ^ 31 from rfl]
    exact land_clear _ 31 32 (by norm_num) (by omega)
  rw [Bool.eq_iff_iff, bne_iff_ne, show Wasm.IEEE64.sign b = true ↔ 2 ^ 63 ≤ b.toNat from by
    unfold Wasm.IEEE64.sign; exact decide_eq_true_iff]
  constructor
  · intro hne
    by_contra hc
    apply hne
    apply UInt64.toNat_inj.mp
    rw [h1, UInt64.toNat_zero]
    omega
  · intro hc h0
    have := congrArg UInt64.toNat h0
    rw [h1, UInt64.toNat_zero] at this
    omega

#print axioms ax_abs
#print axioms neg_flag

/-- `Sinpi.ffloor` on the words of a positive `b` from 1 below `2 ^ 52`: `j0` is the unbiased
exponent, and the integer part keeps the bits of `b` from its units bit up. -/
theorem ffloor_bits (b ix lx : UInt64) (hb : b.toNat < 2 ^ 63)
    (hix : ix.toNat = b.toNat / 2 ^ 32) (hlx : lx.toNat = b.toNat % 2 ^ 32)
    (he1 : 1023 ≤ Wasm.IEEE64.exponent b) (he2 : Wasm.IEEE64.exponent b ≤ 1074) :
    (Sinpi.ffloor ix lx).2.toNat = Wasm.IEEE64.exponent b - 1023 ∧
      (Sinpi.ffloor ix lx).1.toBits.toNat =
        b.toNat / 2 ^ (1075 - Wasm.IEEE64.exponent b) * 2 ^ (1075 - Wasm.IEEE64.exponent b) := by
  have hexp : Wasm.IEEE64.exponent b = b.toNat / 2 ^ 52 := by
    unfold Wasm.IEEE64.exponent; omega
  generalize hE : Wasm.IEEE64.exponent b = e at he1 he2 hexp ⊢
  have hfield : ((ix >>> 20) &&& 0x7ff).toNat = e := by
    rw [UInt64.toNat_and, TrigWords.shr_toNat, show (20 : UInt64).toNat % 64 = 20 from rfl,
      show (0x7ff : UInt64).toNat = 2 ^ 11 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, hix]
    omega
  have hj0 : (((ix >>> 20) &&& 0x7ff) - 0x3ff).toNat = e - 1023 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hfield]; exact he1), hfield]
    rfl
  -- The word with the bits below `2 ^ m` cleared is not a NaN pattern.
  have hnan : ∀ w : UInt64, w.toNat = b.toNat / 2 ^ (1075 - e) * 2 ^ (1075 - e) →
      Wasm.IEEE64.isNaN w = false := by
    intro w hw
    have h1 : w.toNat / 2 ^ 52 = e := by
      have : 2 ^ 52 = 2 ^ (1075 - e) * 2 ^ (52 - (1075 - e)) := by
        rw [← pow_add]; congr 1; omega
      rw [hw]
      conv_rhs => rw [hexp]
      rw [this, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
        Nat.mul_div_cancel _ (by positivity)]
    unfold Wasm.IEEE64.isNaN Wasm.IEEE64.exponent
    have : w.toNat / 2 ^ 52 % 2 ^ 11 = e := by omega
    simp [this]
    omega
  unfold Sinpi.ffloor
  dsimp only
  have hixb : ix.toNat < 2 ^ 31 := by rw [hix]; omega
  have hlxb : lx.toNat < 2 ^ 32 := by rw [hlx]; omega
  split_ifs with hlt
  · have hj : e - 1023 < 20 := by
      rw [UInt64.lt_iff_toNat_lt, hj0] at hlt
      exact hlt
    refine ⟨hj0, ?_⟩
    have hw : ((ix &&& ((0xFFFFFFFF : UInt64) ^^^ ((0x000fffff : UInt64) >>>
        (((ix >>> 20) &&& 0x7ff) - 0x3ff)))) <<< 32).toNat =
        b.toNat / 2 ^ (1075 - e) * 2 ^ (1075 - e) := by
      rw [TrigWords.shl_toNat, show (32 : UInt64).toNat % 64 = 32 from rfl, UInt64.toNat_and,
        UInt64.toNat_xor, TrigWords.shr_toNat, hj0, Nat.mod_eq_of_lt (by omega : e - 1023 < 64),
        show (0x000fffff : UInt64).toNat = 2 ^ 20 - 1 from rfl,
        show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, low_ones 20 _ (by omega),
        xor_mask _ (by omega), land_clear _ _ 32 (by omega) (by omega)]
      have hm : 1075 - e = 32 + (20 - (e - 1023)) := by omega
      rw [hm, pow_add, ← Nat.div_div_eq_div_mul, Nat.mod_eq_of_lt, hix]
      · ring
      · rw [hix]
        have : b.toNat / 2 ^ 32 / 2 ^ (20 - (e - 1023)) * 2 ^ (20 - (e - 1023)) ≤
            b.toNat / 2 ^ 32 := Nat.div_mul_le_self _ _
        omega
    rw [F64Bits.toBits_ofBits, hnan _ hw]
    exact hw
  · have hj : 20 ≤ e - 1023 := by
      rw [UInt64.lt_iff_toNat_lt, hj0] at hlt
      push Not at hlt
      exact hlt
    refine ⟨hj0, ?_⟩
    have hsub : ((((ix >>> 20) &&& 0x7ff) - 0x3ff) - 20).toNat = e - 1023 - 20 := by
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, hj0]; exact hj), hj0]
      rfl
    have hm : (2 : Nat) ^ 32 = 2 ^ (32 - (1075 - e)) * 2 ^ (1075 - e) := by
      rw [← pow_add]; congr 1; omega
    have hlow : (lx &&& ((0xFFFFFFFF : UInt64) ^^^ ((0xffffffff : UInt64) >>>
        ((((ix >>> 20) &&& 0x7ff) - 0x3ff) - 20)))).toNat =
        lx.toNat / 2 ^ (1075 - e) * 2 ^ (1075 - e) := by
      rw [UInt64.toNat_and, UInt64.toNat_xor, TrigWords.shr_toNat, hsub,
        Nat.mod_eq_of_lt (by omega : e - 1023 - 20 < 64),
        show (0xffffffff : UInt64).toNat = 2 ^ 32 - 1 from rfl, low_ones 32 _ (by omega),
        show 32 - (e - 1023 - 20) = 1075 - e by omega, xor_mask _ (by omega),
        land_clear _ _ 32 (by omega) hlxb]
    have hlowb : lx.toNat / 2 ^ (1075 - e) * 2 ^ (1075 - e) < 2 ^ 32 := by
      have := Nat.div_mul_le_self lx.toNat (2 ^ (1075 - e))
      omega
    have hw : ((ix <<< 32) ||| (lx &&& ((0xFFFFFFFF : UInt64) ^^^ ((0xffffffff : UInt64) >>>
        ((((ix >>> 20) &&& 0x7ff) - 0x3ff) - 20))))).toNat =
        b.toNat / 2 ^ (1075 - e) * 2 ^ (1075 - e) := by
      rw [UInt64.toNat_or, hlow, TrigWords.shl_toNat, show (32 : UInt64).toNat % 64 = 32 from rfl,
        Nat.mod_eq_of_lt (by omega), Nat.mul_comm ix.toNat (2 ^ 32),
        ← Nat.two_pow_add_eq_or_of_lt hlowb]
      have hb2 : b.toNat = ix.toNat * 2 ^ 32 + lx.toNat := by rw [hix, hlx]; omega
      have key : (ix.toNat * 2 ^ 32 + lx.toNat) / 2 ^ (1075 - e) =
          ix.toNat * 2 ^ (32 - (1075 - e)) + lx.toNat / 2 ^ (1075 - e) := by
        rw [hm, ← Nat.mul_assoc, Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
          Nat.add_comm]
      rw [hb2, key, Nat.add_mul, hm]
      ring
    rw [F64Bits.toBits_ofBits, hnan _ hw]
    exact hw

#print axioms ffloor_bits

end Verified.Examples.SinpiBits
