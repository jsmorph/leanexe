import Library.Numerics.Float64.Sinh.Compiled
import LeanExe.ProofKit.F64PowerScale
import LeanExe.ProofKit.F64NearestScale

/-!
The words of `Sinh.ldexpExp` with the exponent argument `-1`, which `sinh` and `cosh` use from
`ln (DBL_MAX)` on.  For the word `b` of `exp (a - kln2)` with sign 0, exponent field `E`, and
fraction `F`, `frexpExp` forms the word with exponent field 2046 and fraction `F` (`ybits_eq`),
and `ldexpExp` multiplies it by the word with exponent field `E + 775` and fraction 0
(`sbits_eq`).  The product is `2 ^ 1798` times the value of `b` for `E ≤ 248`
and positive infinity for `E = 249` (`ldexp_value`, `ldexp_overflow`).
-/

namespace Library.Numerics.Float64.Sinh.SinhLdexpBits
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096
set_option maxRecDepth 100000

/-- `k_exp.c`'s `kln2`. -/
def kln2 : UInt64 := 0x40937BE319BA0DA4

def ybits (b : UInt64) : UInt64 :=
  ((((b >>> 32) &&& (0xfffff : UInt64)) ||| ((0x3ff + 1023 : UInt64) <<< 20)) <<< 32) |||
    (b &&& 0xFFFFFFFF)

def sbits (b : UInt64) : UInt64 :=
  let hx : UInt64 := b >>> 32
  let expt : UInt64 := (hx >>> 20) - (0x3ff + 1023 : UInt64) + 1799
  let expt' : UInt64 := (0 - 1 : UInt64) + expt
  (((0x3ff + expt') <<< 20) &&& 0xFFFFFFFF) <<< 32

theorem ldexp_eq (tab : Array UInt64) (a : Float) :
    Sinh.ldexpExp tab a (0 - 1) =
      Float.ofBits (ybits (Exp.expWith tab (a - Float.ofBits kln2)).toBits) *
        Float.ofBits (sbits (Exp.expWith tab (a - Float.ofBits kln2)).toBits) := rfl

theorem word_split (b : UInt64) (hs : b.toNat < 2 ^ 63) :
    b.toNat = Wasm.IEEE64.exponent b * 2 ^ 52 + Wasm.IEEE64.fraction b := by
  unfold Wasm.IEEE64.exponent Wasm.IEEE64.fraction
  omega

theorem or_disjoint (a b i : Nat) (hb : b < 2 ^ i) : a * 2 ^ i ||| b = a * 2 ^ i + b := by
  rw [Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hb]

theorem ybits_eq (b : UInt64) (hs : b.toNat < 2 ^ 63) :
    ybits b = Wasm.IEEE64.encodeFinite false 2046 (Wasm.IEEE64.fraction b) := by
  have hsplit := word_split b hs
  have hF : Wasm.IEEE64.fraction b < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hE : Wasm.IEEE64.exponent b < 2 ^ 11 := Nat.mod_lt _ (by positivity)
  generalize Wasm.IEEE64.exponent b = E at hsplit hE
  generalize Wasm.IEEE64.fraction b = F at hsplit hF ⊢
  apply UInt64.toNat_inj.mp
  simp only [ybits, Wasm.IEEE64.encodeFinite, UInt64.toNat_or, UInt64.toNat_and,
    UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight, UInt64.reduceToNat, UInt64.reduceAdd,
    Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, UInt64.toNat_ofNat',
    Bool.false_eq_true, ite_false, hsplit]
  rw [show (1048575 : Nat) = 2 ^ 20 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod,
    show (4294967295 : Nat) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h1 : (E * 2 ^ 52 + F) / 2 ^ 32 % 2 ^ 20 = F / 2 ^ 32 := by omega
  have h2 : (E * 2 ^ 52 + F) % 2 ^ 32 = F % 2 ^ 32 := by omega
  have h3 : F / 2 ^ 32 < 2 ^ 20 := by omega
  rw [h1, h2, show 2046 * 2 ^ 20 % 2 ^ 64 = 2046 * 2 ^ 20 by norm_num,
    Nat.or_comm (F / 2 ^ 32) (2046 * 2 ^ 20), or_disjoint 2046 _ 20 h3]
  have h5 : 2046 * 2 ^ 20 + F / 2 ^ 32 < 2 ^ 32 := by omega
  have h6 : (2046 * 2 ^ 20 + F / 2 ^ 32) * 2 ^ 32 < 2 ^ 64 := by
    calc _ < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right h5 (by positivity)
      _ = 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt h6, or_disjoint _ _ 32 (Nat.mod_lt _ (by positivity))]
  have h7 : 0 + 2046 * 2 ^ 52 + F < 2 ^ 64 := by
    calc 0 + 2046 * 2 ^ 52 + F < 2047 * 2 ^ 52 := by omega
      _ < 2 ^ 64 := by norm_num
  rw [Nat.mod_eq_of_lt h7, add_mul, add_assoc, Nat.div_add_mod' F (2 ^ 32)]
  norm_num

theorem sbits_eq (b : UInt64) (hs : b.toNat < 2 ^ 63) :
    sbits b = Wasm.IEEE64.encodeFinite false (Wasm.IEEE64.exponent b + 775) 0 := by
  have hsplit := word_split b hs
  have hF : Wasm.IEEE64.fraction b < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hE : Wasm.IEEE64.exponent b < 2 ^ 11 := Nat.mod_lt _ (by positivity)
  generalize Wasm.IEEE64.exponent b = E at hsplit hE ⊢
  generalize Wasm.IEEE64.fraction b = F at hsplit hF
  apply UInt64.toNat_inj.mp
  simp only [sbits, Wasm.IEEE64.encodeFinite, UInt64.toNat_and, UInt64.toNat_shiftLeft,
    UInt64.toNat_add, UInt64.toNat_sub, UInt64.toNat_shiftRight, UInt64.reduceToNat,
    UInt64.reduceAdd, Nat.reduceMod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    UInt64.toNat_ofNat', Bool.false_eq_true, ite_false, hsplit]
  rw [show (4294967295 : Nat) = 2 ^ 32 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
  have h1 : (E * 2 ^ 52 + F) / 2 ^ 32 / 2 ^ 20 = E := by omega
  rw [h1]
  omega

/-- The product for `E ≤ 248`: finite, `2 ^ 1798` times the value of `b`. -/
theorem ldexp_value (b : UInt64) (hs : Wasm.IEEE64.sign b = false)
    (hE1 : 247 ≤ Wasm.IEEE64.exponent b) (hE2 : Wasm.IEEE64.exponent b ≤ 248) :
    Finite (Wasm.IEEE64.mul (ybits b) (sbits b)) ∧
      value (Wasm.IEEE64.mul (ybits b) (sbits b)) = 2 ^ 1798 * value b := by
  have hs63 : b.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  rw [ybits_eq b hs63, sbits_eq b hs63]
  set F := Wasm.IEEE64.fraction b
  set E := Wasm.IEEE64.exponent b
  have hF : F < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hYn : (Wasm.IEEE64.encodeFinite false 2046 F).toNat = 2046 * 2 ^ 52 + F := by
    simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add,
      UInt64.toNat_ofNat']
    omega
  have hYe : Wasm.IEEE64.exponent (Wasm.IEEE64.encodeFinite false 2046 F) = 2046 := by
    unfold Wasm.IEEE64.exponent; rw [hYn]; omega
  have hYf : Wasm.IEEE64.fraction (Wasm.IEEE64.encodeFinite false 2046 F) = F := by
    unfold Wasm.IEEE64.fraction; rw [hYn]; omega
  have hYfin : Finite (Wasm.IEEE64.encodeFinite false 2046 F) := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hYe]; decide
  have hPf : Finite (Wasm.IEEE64.encodeFinite false (E + 775) 0) := by
    have hn : (Wasm.IEEE64.encodeFinite false (E + 775) 0).toNat = (E + 775) * 2 ^ 52 := by
      simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add, add_zero,
        UInt64.toNat_ofNat']
      omega
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, hn,
      bne_iff_ne, ne_eq]
    omega
  rw [F64NearestScale.mul_comm_finite _ _ hYfin hPf]
  obtain ⟨hf, hv⟩ := F64PowerScale.mul_power_finite (E + 775) _ (by omega) (by omega) hYfin
    (by omega) (by omega) (by omega)
  refine ⟨hf, ?_⟩
  rw [hv]
  have hbl : b.toNat < F64NearestNonnegative.limit := by
    have := word_split b hs63
    unfold F64NearestNonnegative.limit
    omega
  have hYl : (Wasm.IEEE64.encodeFinite false 2046 F).toNat < F64NearestNonnegative.limit := by
    rw [hYn]; unfold F64NearestNonnegative.limit; omega
  have hvY : value (Wasm.IEEE64.encodeFinite false 2046 F) =
      ((2 : ℝ) ^ 52 + F) * 2 ^ 2045 / 2 ^ 1074 := by
    rw [F64NearestScale.normal_value' _ hYl (by omega), hYe, hYf,
      show (2046 : Nat) - 1 = 2045 from rfl]
    push_cast
    ring
  have hvb : value b = ((2 : ℝ) ^ 52 + F) * 2 ^ (E - 1) / 2 ^ 1074 := by
    rw [F64NearestScale.normal_value' _ hbl (by omega)]
    push_cast
    ring
  have hz : ((E + 775 : Nat) : Int) - 1023 = (E : Int) - 248 := by push_cast; ring
  rw [hz, hvY, hvb]
  have hpow : (2 : ℝ) ^ ((E : Int) - 248) * 2 ^ 2045 = 2 ^ 1798 * 2 ^ (E - 1) := by
    rw [← zpow_natCast (2 : ℝ) 2045, ← zpow_natCast (2 : ℝ) 1798,
      ← zpow_natCast (2 : ℝ) (E - 1), ← zpow_add₀ two_ne_zero, ← zpow_add₀ two_ne_zero]
    have he : (E : ℤ) - 248 + ((2045 : ℕ) : ℤ) = ((1798 : ℕ) : ℤ) + ((E - 1 : ℕ) : ℤ) := by
      omega
    rw [he]
  calc (2 : ℝ) ^ ((E : Int) - 248) * (((2 : ℝ) ^ 52 + F) * 2 ^ 2045 / 2 ^ 1074)
      = ((2 : ℝ) ^ 52 + F) * ((2 : ℝ) ^ ((E : Int) - 248) * 2 ^ 2045) / 2 ^ 1074 := by ring
    _ = 2 ^ 1798 * (((2 : ℝ) ^ 52 + F) * 2 ^ (E - 1) / 2 ^ 1074) := by rw [hpow]; ring

/-- The product for `E = 249`: positive infinity. -/
theorem ldexp_overflow (b : UInt64) (hs : Wasm.IEEE64.sign b = false)
    (hE : Wasm.IEEE64.exponent b = 249) :
    Wasm.IEEE64.mul (ybits b) (sbits b) = 0x7FF0000000000000 := by
  have hs63 : b.toNat < 2 ^ 63 := by
    simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hs
    exact hs
  rw [ybits_eq b hs63, sbits_eq b hs63, hE]
  set F := Wasm.IEEE64.fraction b
  have hF : F < 2 ^ 52 := Nat.mod_lt _ (by positivity)
  have hYn : (Wasm.IEEE64.encodeFinite false 2046 F).toNat = 2046 * 2 ^ 52 + F := by
    simp only [Wasm.IEEE64.encodeFinite, Bool.false_eq_true, ite_false, zero_add,
      UInt64.toNat_ofNat']
    omega
  have hYe : Wasm.IEEE64.exponent (Wasm.IEEE64.encodeFinite false 2046 F) = 2046 := by
    unfold Wasm.IEEE64.exponent; rw [hYn]; omega
  have hYs : Wasm.IEEE64.sign (Wasm.IEEE64.encodeFinite false 2046 F) = false := by
    simp only [Wasm.IEEE64.sign, hYn, decide_eq_false_iff_not, not_le]; omega
  have hYfin : Finite (Wasm.IEEE64.encodeFinite false 2046 F) := by
    simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, hYe]; decide
  have hPf : Finite (Wasm.IEEE64.encodeFinite false (249 + 775) 0) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  rw [F64NearestScale.mul_comm_finite _ _ hYfin hPf,
    F64PowerScale.mul_power_overflow (249 + 775) _ (by norm_num) (by norm_num) hYfin
      (by omega) (by omega) (by omega), hYs]
  decide

#print axioms ldexp_eq
#print axioms ybits_eq
#print axioms sbits_eq
#print axioms ldexp_value
#print axioms ldexp_overflow

end Library.Numerics.Float64.Sinh.SinhLdexpBits
