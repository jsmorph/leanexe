import Verified.Examples.Log10
import Verified.Examples.Log2Power
import Verified.Examples.LogBranches
import LeanExe.ProofKit.F64HighWord

/-!
The word arithmetic of `Log10.log10`.  On the main path the code takes the high word `hx` of the
argument, scaled by `2 ^ 54` if it is subnormal, and forms `x' = 2 ^ -k x` with the exponent field
of `x'` 1023 or 1022: 1022 when the top 20 fraction bits reach `0x6a09c`, the fraction of `√2`.
`xr_fields` gives the word of `x'` and the word of `k` from the exponent field `E` and fraction
field `F` of the argument.  `tailWord` is the arithmetic after `f = x' - 1` and the double `y` of
`k`, and the branch lemmas restate `Log10.log10` through it.
-/

namespace Verified.Examples.Log10Bits
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- `Log10.kLog1p` on words. -/
def kWord (f : UInt64) : UInt64 :=
  let s := Wasm.IEEE64.div f (Wasm.IEEE64.add 0x4000000000000000 f)
  let z := Wasm.IEEE64.mul s s
  let w := Wasm.IEEE64.mul z z
  let t1 := Wasm.IEEE64.mul w (Wasm.IEEE64.add 0x3FD999999997FA04
    (Wasm.IEEE64.mul w (Wasm.IEEE64.add 0x3FCC71C51D8E78AF (Wasm.IEEE64.mul w 0x3FC39A09D078C69F))))
  let t2 := Wasm.IEEE64.mul z (Wasm.IEEE64.add 0x3FE5555555555593
    (Wasm.IEEE64.mul w (Wasm.IEEE64.add 0x3FD2492494229359
      (Wasm.IEEE64.mul w (Wasm.IEEE64.add 0x3FC7466496CB03DE
        (Wasm.IEEE64.mul w 0x3FC2F112DF3E5244))))))
  let R := Wasm.IEEE64.add t2 t1
  let hfsq := Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000 f) f
  Wasm.IEEE64.mul s (Wasm.IEEE64.add hfsq R)

theorem kLog1p_bits (f : Float) : (Log10.kLog1p f).toBits = kWord f.toBits := by
  have h2 : (2.0 : Float).toBits = 0x4000000000000000 := rfl
  have h5 : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
  have n1 : Wasm.IEEE64.isNaN 0x3FE5555555555593 = false := by decide
  have n2 : Wasm.IEEE64.isNaN 0x3FD999999997FA04 = false := by decide
  have n3 : Wasm.IEEE64.isNaN 0x3FD2492494229359 = false := by decide
  have n4 : Wasm.IEEE64.isNaN 0x3FCC71C51D8E78AF = false := by decide
  have n5 : Wasm.IEEE64.isNaN 0x3FC7466496CB03DE = false := by decide
  have n6 : Wasm.IEEE64.isNaN 0x3FC39A09D078C69F = false := by decide
  have n7 : Wasm.IEEE64.isNaN 0x3FC2F112DF3E5244 = false := by decide
  simp only [Log10.kLog1p, kWord, F64Bits.toBits_add, F64Bits.toBits_mul, F64Bits.toBits_div,
    F64Bits.toBits_ofBits, h2, h5, n1, n2, n3, n4, n5, n6, n7, Bool.false_eq_true, ↓reduceIte]

/-- The arithmetic of `Log10.log10` after `f = x' - 1` and `y = k`. -/
def tailWord (f y : UInt64) : UInt64 :=
  let hfsq := Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000 f) f
  let r := kWord f
  let hi := F64HighWord.high (Wasm.IEEE64.sub f hfsq)
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.sub (Wasm.IEEE64.sub f hi) hfsq) r
  let valHi := Wasm.IEEE64.mul hi 0x3FDBCB7B15200000
  let y2 := Wasm.IEEE64.mul y 0x3FD34413509F6000
  let valLo := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.mul y 0x3D59FEF311F12B36)
    (Wasm.IEEE64.mul (Wasm.IEEE64.add lo hi) 0x3DBB9438CA9AADD5))
    (Wasm.IEEE64.mul lo 0x3FDBCB7B15200000)
  let w := Wasm.IEEE64.add y2 valHi
  Wasm.IEEE64.add (Wasm.IEEE64.add valLo (Wasm.IEEE64.add (Wasm.IEEE64.sub y2 w) valHi)) w

/-- The word of `x'`. -/
def xrOf (xw : UInt64) : UInt64 :=
  (((xw >>> 32 &&& (0x000fffff : UInt64)) |||
      ((xw >>> 32 &&& (0x000fffff : UInt64)) + (0x95f64 : UInt64) &&& (0x100000 : UInt64) ^^^
        (0x3ff00000 : UInt64))) <<< 32) |||
    (xw &&& (0xFFFFFFFF : UInt64))

/-- The word of `k`, from the word `k0` of the scaling. -/
def kWord10 (xw k0 : UInt64) : UInt64 :=
  k0 + (xw >>> 32 >>> 20) - (1023 : UInt64) +
    ((xw >>> 32 &&& (0x000fffff : UInt64)) + (0x95f64 : UInt64) &&& (0x100000 : UInt64)) >>> 20

theorem and_bit20 (n : Nat) (hn : n < 2 ^ 21) : n &&& 1048576 = n / 1048576 * 1048576 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, show (1048576 : Nat) = 2 ^ 20 by norm_num, Nat.testBit_two_pow,
    Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j = 20
  · subst hj
    simp
  · by_cases hj2 : 20 ≤ j
    · have h1 : n.testBit j = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le hn (Nat.pow_le_pow_right (by norm_num) (by omega)))
      have he : 20 + (j - 20) = j := by omega
      have he2 : j - 20 + 20 = j := by omega
      simp [Ne.symm hj, he, he2, h1]
    · simp [hj, Ne.symm hj, hj2]

/-- The fields of `x'` and `k` for an argument word with exponent field `E` from 1 to 2046 and
fraction field `F`: `x'` has exponent field `1023 - b` and fraction field `F`, and
`k = k0 + E - 1023 + b`, where `b` is 1 when the top 20 bits of `F` reach `0x6a09c`. -/
theorem xr_fields (xw k0 : UInt64) (E F : Nat) (K0 : Int) (hE1 : 1 ≤ E) (hE2 : E ≤ 2046)
    (hF : F < 4503599627370496) (hxw : xw.toNat = E * 4503599627370496 + F)
    (hk0 : (k0.toNat : Int) = K0 % 18446744073709551616) :
    (xrOf xw).toNat =
        (1023 - (F / 4294967296 + 614244) / 1048576) * 4503599627370496 + F ∧
      ((kWord10 xw k0).toNat : Int) =
        (K0 + E - 1023 + ((F / 4294967296 + 614244) / 1048576 : Nat)) % 18446744073709551616 ∧
      (F / 4294967296 + 614244) / 1048576 ≤ 1 := by
  have hk0lt := k0.toNat_lt
  set G := F / 4294967296 with hG
  have hGlt : G < 1048576 := by omega
  have hhx : (xw >>> 32).toNat = E * 1048576 + G := by
    simp only [UInt64.toNat_shiftRight, UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow,
      Nat.reducePow, hxw]
    omega
  have hG' : (xw >>> 32 &&& (0x000fffff : UInt64)).toNat = G := by
    rw [UInt64.toNat_and, hhx, show (0x000fffff : UInt64).toNat = 2 ^ 20 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod]
    omega
  have hsum : ((xw >>> 32 &&& (0x000fffff : UInt64)) + (0x95f64 : UInt64)).toNat = G + 614244 := by
    rw [UInt64.toNat_add, hG']
    simp only [UInt64.reduceToNat]
    omega
  set b := (G + 614244) / 1048576 with hb
  have hb1 : b ≤ 1 := by omega
  have hi : ((xw >>> 32 &&& (0x000fffff : UInt64)) + (0x95f64 : UInt64) &&& (0x100000 : UInt64)).toNat = b * 1048576 := by
    rw [UInt64.toNat_and, hsum, show (0x100000 : UInt64).toNat = 1048576 by decide,
      and_bit20 _ (by omega)]
  have hxor : ((xw >>> 32 &&& (0x000fffff : UInt64)) + (0x95f64 : UInt64) &&& (0x100000 : UInt64) ^^^ (0x3ff00000 : UInt64)).toNat =
      (1023 - b) * 1048576 := by
    rw [UInt64.toNat_xor, hi, show (0x3ff00000 : UInt64).toNat = 1072693248 by decide]
    rcases Nat.lt_or_ge b 1 with h | h
    · have : b = 0 := by omega
      rw [this]
      decide
    · have : b = 1 := by omega
      rw [this]
      decide
  have hor : ((xw >>> 32 &&& (0x000fffff : UInt64)) |||
      ((xw >>> 32 &&& (0x000fffff : UInt64)) + (0x95f64 : UInt64) &&& (0x100000 : UInt64) ^^^ (0x3ff00000 : UInt64))).toNat =
      (1023 - b) * 1048576 + G := by
    rw [UInt64.toNat_or, hG', hxor, Nat.or_comm, show (1023 - b) * 1048576 = 2 ^ 20 * (1023 - b) by ring,
      ← Nat.two_pow_add_eq_or_of_lt (by omega : G < 2 ^ 20)]
  have hshl : (((xw >>> 32 &&& (0x000fffff : UInt64)) |||
      ((xw >>> 32 &&& (0x000fffff : UInt64)) + (0x95f64 : UInt64) &&& (0x100000 : UInt64) ^^^ (0x3ff00000 : UInt64))) <<< 32).toNat =
      ((1023 - b) * 1048576 + G) * 4294967296 := by
    rw [UInt64.toNat_shiftLeft, hor]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftLeft_eq, Nat.reducePow]
    apply Nat.mod_eq_of_lt
    have : (1023 - b) * 1048576 + G < 1073741824 := by omega
    calc ((1023 - b) * 1048576 + G) * 4294967296 < 1073741824 * 4294967296 :=
          Nat.mul_lt_mul_of_pos_right this (by norm_num)
      _ < 18446744073709551616 := by norm_num
  have hlow : (xw &&& (0xFFFFFFFF : UInt64)).toNat = F % 4294967296 := by
    rw [UInt64.toNat_and, show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 by decide,
      Nat.and_two_pow_sub_one_eq_mod, hxw]
    omega
  refine ⟨?_, ?_, hb1⟩
  · simp only [xrOf]
    rw [UInt64.toNat_or, hshl, hlow,
      show ((1023 - b) * 1048576 + G) * 4294967296 = 2 ^ 32 * ((1023 - b) * 1048576 + G) by ring,
      ← Nat.two_pow_add_eq_or_of_lt (by omega : F % 4294967296 < 2 ^ 32)]
    simp only [Nat.reducePow]
    omega
  · have hE : (xw >>> 32 >>> 20).toNat = E := by
      rw [UInt64.toNat_shiftRight, hhx]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      omega
    have hb' : (((xw >>> 32 &&& (0x000fffff : UInt64)) + (0x95f64 : UInt64) &&& (0x100000 : UInt64)) >>> 20).toNat = b := by
      rw [UInt64.toNat_shiftRight, hi]
      simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, Nat.reducePow]
      omega
    simp only [kWord10]
    rw [UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_add, hE, hb']
    simp only [UInt64.reduceToNat, Nat.reducePow]
    omega

theorem kd_ite (k : UInt64) :
    (if k >>> 63 == 1 then -(0 - k).toFloat else k.toFloat).toBits = Log2Power.kdBits k :=
  Log2Power.kd_bits k

/-- `Log10.log10` on a positive normal argument other than 1 below infinity. -/
theorem normal_bits (x : Float)
    (hneg : (x.toBits >>> 32 >>> 31 == 1) = false)
    (hlo : ¬ x.toBits >>> 32 < 0x00100000)
    (hinf : ¬ x.toBits >>> 32 ≥ 0x7ff00000)
    (hone : (x.toBits >>> 32 == 0x3ff00000 && x.toBits &&& (0xFFFFFFFF : UInt64) == 0) = false)
    (hxr : Wasm.IEEE64.isNaN (xrOf x.toBits) = false)
    (hhi : Wasm.IEEE64.isNaN (Wasm.IEEE64.sub (Wasm.IEEE64.sub (xrOf x.toBits) 0x3FF0000000000000)
      (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000
        (Wasm.IEEE64.sub (xrOf x.toBits) 0x3FF0000000000000))
        (Wasm.IEEE64.sub (xrOf x.toBits) 0x3FF0000000000000)) &&& (0xFFFFFFFF00000000 : UInt64)) = false) :
    (Log10.log10 x).toBits =
      tailWord (Wasm.IEEE64.sub (xrOf x.toBits) 0x3FF0000000000000)
        (Log2Power.kdBits (kWord10 x.toBits 0)) := by
  have h1 : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have h5 : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
  have c1 : Wasm.IEEE64.isNaN 0x3FDBCB7B15200000 = false := by decide
  have c2 : Wasm.IEEE64.isNaN 0x3DBB9438CA9AADD5 = false := by decide
  have c3 : Wasm.IEEE64.isNaN 0x3FD34413509F6000 = false := by decide
  have c4 : Wasm.IEEE64.isNaN 0x3D59FEF311F12B36 = false := by decide
  simp only [xrOf] at hxr hhi
  simp only [Log10.log10, hneg, hlo, hinf, hone, decide_false, Bool.false_or, Bool.false_and,
    Bool.false_eq_true,
    ↓reduceIte, F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul, F64Bits.toBits_ofBits,
    kLog1p_bits, kd_ite, h1, h5, c1, c2, c3, c4, hxr, hhi, tailWord, xrOf, kWord10,
    F64HighWord.high]

#print axioms kLog1p_bits
#print axioms and_bit20
#print axioms xr_fields
#print axioms normal_bits

/-- `Log10.log10` on a positive subnormal argument, scaled by `2 ^ 54`. -/
theorem subnormal_bits (x : Float)
    (hneg : (x.toBits >>> 32 >>> 31 == 1) = false)
    (hlo : x.toBits >>> 32 < 0x00100000)
    (hz : ((x.toBits >>> 32 &&& (0x7fffffff : UInt64)) ||| (x.toBits &&& (0xFFFFFFFF : UInt64)) == 0) = false)
    (hinf : ¬ Wasm.IEEE64.mul x.toBits 0x4350000000000000 >>> 32 ≥ 0x7ff00000)
    (hone : (Wasm.IEEE64.mul x.toBits 0x4350000000000000 >>> 32 == 0x3ff00000 &&
      x.toBits &&& (0xFFFFFFFF : UInt64) == 0) = false)
    (hxr : Wasm.IEEE64.isNaN (xrOf (Wasm.IEEE64.mul x.toBits 0x4350000000000000)) = false)
    (hhi : Wasm.IEEE64.isNaN (Wasm.IEEE64.sub
      (Wasm.IEEE64.sub (xrOf (Wasm.IEEE64.mul x.toBits 0x4350000000000000)) 0x3FF0000000000000)
      (Wasm.IEEE64.mul (Wasm.IEEE64.mul 0x3FE0000000000000
        (Wasm.IEEE64.sub (xrOf (Wasm.IEEE64.mul x.toBits 0x4350000000000000)) 0x3FF0000000000000))
        (Wasm.IEEE64.sub (xrOf (Wasm.IEEE64.mul x.toBits 0x4350000000000000)) 0x3FF0000000000000))
      &&& (0xFFFFFFFF00000000 : UInt64)) = false) :
    (Log10.log10 x).toBits =
      tailWord (Wasm.IEEE64.sub (xrOf (Wasm.IEEE64.mul x.toBits 0x4350000000000000))
          0x3FF0000000000000)
        (Log2Power.kdBits (kWord10 (Wasm.IEEE64.mul x.toBits 0x4350000000000000) (0 - 54))) := by
  have h1 : (1.0 : Float).toBits = 0x3FF0000000000000 := rfl
  have h5 : (0.5 : Float).toBits = 0x3FE0000000000000 := rfl
  have c0 : Wasm.IEEE64.isNaN 0x4350000000000000 = false := by decide
  have c1 : Wasm.IEEE64.isNaN 0x3FDBCB7B15200000 = false := by decide
  have c2 : Wasm.IEEE64.isNaN 0x3DBB9438CA9AADD5 = false := by decide
  have c3 : Wasm.IEEE64.isNaN 0x3FD34413509F6000 = false := by decide
  have c4 : Wasm.IEEE64.isNaN 0x3D59FEF311F12B36 = false := by decide
  simp only [xrOf] at hxr hhi
  simp only [Log10.log10, hneg, hlo, hz, hinf, hone, decide_true, Bool.false_or, Bool.true_and,
    Bool.false_eq_true, ↓reduceIte, F64Bits.toBits_add, F64Bits.toBits_sub, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, kLog1p_bits, kd_ite, h1, h5, c0, c1, c2, c3, c4, hxr, hhi, tailWord,
    xrOf, kWord10, F64HighWord.high]

/-- `(x - x) / 0` for a NaN, a finite `x`, or negative infinity is the canonical NaN. -/
theorem invalid10_bits (x : Float) (h : Wasm.IEEE64.isNaN x.toBits = true ∨ Finite x.toBits ∨
    x.toBits = 0xFFF0000000000000) :
    ((x - x) / 0.0).toBits = Wasm.IEEE64.canonicalNaN := by
  have h0 : (0.0 : Float).toBits = 0 := rfl
  rw [F64Bits.toBits_div, F64Bits.toBits_sub, h0]
  rcases h with h | h | h
  · have hc : Wasm.IEEE64.sub x.toBits x.toBits = Wasm.IEEE64.canonicalNaN := by
      simp only [Wasm.IEEE64.sub, Wasm.IEEE64.add, h, Bool.true_or, ↓reduceIte]
    rw [hc]
    decide +kernel
  · rw [LogBranches.sub_self_finite _ h]
    decide +kernel
  · rw [h]
    decide +kernel

#print axioms subnormal_bits
#print axioms invalid10_bits

end Verified.Examples.Log10Bits
