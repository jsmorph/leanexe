import Verified.Examples.ErfcRound
import Verified.Examples.ErfcCast

/-!
The integer steps of `exp_1` and `exp_accurate` in `Erfc`.  For a negative integer `K = -n`,
`Erfc.toWord` gives the two's complement word `2^64 - n`, and `Erfc.sar` shifts it arithmetically:
`sar_neg` gives `2^64 - 1 - (n - 1)/2^s`.  `split_k` splits `K` into `4096 (m - 1023) + 64 i2 + i1`
with `m`, `i2`, and `i1` as `exp_1` computes them, and `pow2_word` gives the value `2^(m - 1023)` of
the word `m << 52`.
-/

namespace Verified.Examples.ErfcExpBits

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcOps ErfcRound PolyBound

set_option exponentiation.threshold 2200

theorem xor_ones (a : UInt64) : (a ^^^ 0xFFFFFFFFFFFFFFFF).toNat = 2 ^ 64 - 1 - a.toNat := by
  have h1 : (a ^^^ 0xFFFFFFFFFFFFFFFF).toBitVec = ~~~a.toBitVec := by
    rw [UInt64.toBitVec_xor, show (0xFFFFFFFFFFFFFFFF : UInt64).toBitVec = BitVec.allOnes 64 by
      decide]
    exact BitVec.xor_allOnes
  rw [← UInt64.toNat_toBitVec, h1, BitVec.toNat_not, UInt64.toNat_toBitVec]

/-- The arithmetic shift of a negative word. -/
theorem sar_neg (kw : UInt64) (n s : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 2 ^ 62) (hs : s < 64)
    (hk : kw.toNat = 2 ^ 64 - n) :
    (Erfc.sar kw (UInt64.ofNat s)).toNat = 2 ^ 64 - 1 - (n - 1) / 2 ^ s := by
  have hs' : (UInt64.ofNat s).toNat % 64 = s := by
    rw [UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]; omega
  unfold Erfc.sar
  rw [sign_bit, show decide (2 ^ 63 ≤ kw.toNat) = true from decide_eq_true (by omega), if_pos rfl,
    xor_ones, UInt64.toNat_shiftRight, hs', Nat.shiftRight_eq_div_pow, xor_ones, hk]
  congr 2
  omega

/-- The two's complement word of a negative integer-valued float. -/
theorem toWord_neg (v : Float) (hv : ff v) (n : ℕ) (hvn : fv v = -(n : ℝ)) (hn1 : 1 ≤ n)
    (hn2 : n < 2 ^ 63) : (Erfc.toWord v).toNat = 2 ^ 64 - n := by
  obtain ⟨z0f, z0v⟩ : ff (0.0 : Float) ∧ fv (0.0 : Float) = 0 := by
    have hb : (0.0 : Float).toBits = 0 := rfl
    unfold ff fv; rw [hb]
    exact ⟨by unfold CodeLib.IEEE64.Finite; decide +kernel, by simp [value,
      Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.exponent,
      Wasm.IEEE64.fraction, Wasm.IEEE64.sign]⟩
  have hneg : v < 0.0 := (flt_iff _ _ hv z0f).mpr (by
    rw [hvn, z0v]; have : (1 : ℝ) ≤ n := by qc hn1
    linarith)
  obtain ⟨nf, nv⟩ := neg_f v hv
  have hu : (-v).toUInt64 = UInt64.ofNat n :=
    SinpiFloor.toUInt64_int (-v) n nf (by show fv (-v) = n; rw [nv, hvn]; ring) hn1 hn2
  unfold Erfc.toWord
  rw [ite_eq_left hneg, hu, UInt64.toNat_sub, UInt64.toNat_ofNat_of_lt' (by
    rw [show UInt64.size = 2 ^ 64 from rfl]; omega)]
  have h0 : (0 : UInt64).toNat = 0 := rfl
  rw [h0]
  omega

/-- `K = -n` splits into `4096 (m - 1023) + 64 i2 + i1` with `m`, `i2`, `i1` as `exp_1` computes them
from the two's complement word `kw` of `K`. -/
theorem split_k (kw : UInt64) (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 4096 * 1022)
    (hk : kw.toNat = 2 ^ 64 - n) :
    (Erfc.sar kw 12 + 0x3ff).toNat = 1022 - (n - 1) / 4096 ∧
      (Erfc.sar kw 6 &&& 0x3f).toNat = 63 - (n - 1) / 64 % 64 ∧
      (kw &&& 0x3f).toNat = 63 - (n - 1) % 64 ∧
      -(n : ℤ) = 4096 * ((1022 - (n - 1) / 4096 : ℕ) - 1023 : ℤ) +
        64 * ((63 - (n - 1) / 64 % 64 : ℕ) : ℤ) + ((63 - (n - 1) % 64 : ℕ) : ℤ) := by
  have h12 := sar_neg kw n 12 hn1 (by omega) (by norm_num) hk
  have h6 := sar_neg kw n 6 hn1 (by omega) (by norm_num) hk
  rw [show (UInt64.ofNat 12) = 12 from rfl] at h12
  rw [show (UInt64.ofNat 6) = 6 from rfl] at h6
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [UInt64.toNat_add, h12, show (0x3ff : UInt64).toNat = 1023 from rfl]
    omega
  · rw [UInt64.toNat_and, h6, show (0x3f : UInt64).toNat = 63 from rfl,
      show (63 : ℕ) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  · rw [UInt64.toNat_and, hk, show (0x3f : UInt64).toNat = 63 from rfl,
      show (63 : ℕ) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    omega
  · have : (n - 1) / 4096 ≤ 1021 := by omega
    have e1 : n - 1 = 4096 * ((n - 1) / 4096) + 64 * ((n - 1) / 64 % 64) + (n - 1) % 64 := by
      omega
    push_cast [Nat.sub_le_iff_le_add, show (n - 1) / 4096 ≤ 1022 by omega,
      show (n - 1) / 64 % 64 ≤ 63 by omega, show (n - 1) % 64 ≤ 63 by omega]
    omega

/-- The word `m << 52` for `1 ≤ m ≤ 2046` holds `2^(m - 1023)`. -/
theorem pow2_word (m : UInt64) (h1 : 1 ≤ m.toNat) (h2 : m.toNat ≤ 2046) :
    ff (Float.ofBits (m <<< 52)) ∧
      fv (Float.ofBits (m <<< 52)) = 2 ^ m.toNat / 2 ^ 1023 := by
  have hw : (m <<< 52).toNat = m.toNat * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, show (52 : UInt64).toNat % 64 = 52 from rfl, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have he : Wasm.IEEE64.exponent (m <<< 52) = m.toNat := by
    unfold Wasm.IEEE64.exponent; rw [hw]; omega
  have hf : Wasm.IEEE64.fraction (m <<< 52) = 0 := by
    unfold Wasm.IEEE64.fraction; rw [hw]; omega
  have hs : Wasm.IEEE64.sign (m <<< 52) = false := by
    unfold Wasm.IEEE64.sign; rw [hw]; simp; omega
  have hfin : Finite (m <<< 52) := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite; rw [he]; simp; omega
  obtain ⟨a, b⟩ := ofBits_ff _ hfin
  refine ⟨a, ?_⟩
  rw [b, ratOfWord_cast]
  simp only [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, he, hf, hs]
  have hm0 : m.toNat ≠ 0 := by omega
  simp only [beq_iff_eq, hm0, ite_false, add_zero, Bool.false_eq_true, Int.cast_natCast]
  push_cast
  have hk := pow_succ' (2 : ℝ) (m.toNat - 1)
  rw [Nat.sub_add_cancel h1] at hk
  rw [hk]
  have e : (4503599627370496 : ℝ) / 2 ^ 1074 = 2 / 2 ^ 1023 := by norm_num
  calc (4503599627370496 : ℝ) * 2 ^ (m.toNat - 1) / 2 ^ 1074 =
        2 ^ (m.toNat - 1) * (4503599627370496 / 2 ^ 1074) := by ring
    _ = 2 ^ (m.toNat - 1) * (2 / 2 ^ 1023) := by rw [e]
    _ = 2 * 2 ^ (m.toNat - 1) / 2 ^ 1023 := by ring

/-- A product by a power of two on the right is exact while its exponent stays in range. -/
theorem mul_pow2_right (x p : Float) (hx : ff x) (hp : ff p) (k : ℕ)
    (hpm : Wasm.IEEE64.scaledMagnitude p.toBits = 2 ^ k) (hs : 1074 ≤ gx x.toBits + k)
    (hs2 : gx x.toBits + k ≤ 1074 + 2043) : ff (x * p) ∧ fv (x * p) = fv x * fv p := by
  obtain ⟨m, hm, hm53⟩ := mag_form x.toBits
  have h := F64ExactProduct.mul_exact_scaled x.toBits p.toBits hx hp m 1 (gx x.toBits) k hm
    (by rw [hpm]; ring) (by omega) hs hs2
  unfold ff fv
  rw [F64Bits.toBits_mul]
  exact ⟨h.1, h.2.1⟩

theorem pow2_mag (m : UInt64) (h1 : 1 ≤ m.toNat) (h2 : m.toNat ≤ 2046) :
    Wasm.IEEE64.scaledMagnitude (Float.ofBits (m <<< 52)).toBits = 2 ^ (m.toNat + 51) := by
  have hw : (m <<< 52).toNat = m.toNat * 2 ^ 52 := by
    rw [UInt64.toNat_shiftLeft, show (52 : UInt64).toNat % 64 = 52 from rfl, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by omega)
  have he : Wasm.IEEE64.exponent (m <<< 52) = m.toNat := by
    unfold Wasm.IEEE64.exponent; rw [hw]; omega
  have hf : Wasm.IEEE64.fraction (m <<< 52) = 0 := by
    unfold Wasm.IEEE64.fraction; rw [hw]; omega
  have hfin : Finite (m <<< 52) := by
    unfold CodeLib.IEEE64.Finite Wasm.IEEE64.isFinite; rw [he]; simp; omega
  rw [F64Bits.toBits_ofBits, not_nan_of_finite hfin]
  simp only [Bool.false_eq_true, ite_false]
  unfold Wasm.IEEE64.scaledMagnitude
  simp only [he, hf]
  have hm0 : m.toNat ≠ 0 := by omega
  simp only [beq_iff_eq, hm0, ite_false, add_zero]
  rw [show m.toNat + 51 = 52 + (m.toNat - 1) by omega, pow_add]

#print axioms sar_neg
#print axioms toWord_neg
#print axioms split_k
#print axioms pow2_word

end Verified.Examples.ErfcExpBits
