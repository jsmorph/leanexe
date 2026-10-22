import Library.Numerics.Float64.Asinh.AsinhTheoremBranches
import Library.Numerics.Float64.Log1p.Log1pTheoremReduce

/-!
The main branch of `Asinh.atanh` as an equation.  The code forms `|x|` as the word
`(ix <<< 32) ||| lx`, which `abs_word` identifies with `x.abs`; `atanhT x` is the value of
`atanh |x|` before the sign: `log1p (2 |x| + 2 |x|²/(1 - |x|))/2` below `1/2` and
`log1p (2 |x|/(1 - |x|))/2` from there.
-/

namespace Library.Numerics.Float64.Asinh.AtanhTheoremBranches
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Atan.AtanTheoremBranches

set_option exponentiation.threshold 4096

/-- `atanh |x|` before the sign. -/
def atanhT (x : Float) : Float :=
  if ixOf x < 0x3fe00000 then
    0.5 * Log1p.log1p (x.abs + x.abs + (x.abs + x.abs) * x.abs / (1.0 - x.abs))
  else 0.5 * Log1p.log1p ((x.abs + x.abs) / (1.0 - x.abs))

theorem abs_word_nat (w : UInt64) :
    ((((w >>> 32) &&& 0x7fffffff) <<< 32) ||| (w &&& 0xFFFFFFFF)).toNat = w.toNat % 2 ^ 63 := by
  have hw := w.toNat_lt
  have hl := Library.Numerics.Float64.Log1p.Log1pTheoremReduce.low_nat w
  have hix : ((w >>> 32) &&& 0x7fffffff).toNat = w.toNat / 2 ^ 32 % 2 ^ 31 := by
    simp only [UInt64.toNat_and, UInt64.toNat_shiftRight,
      show (32 : UInt64).toNat % 64 = 32 from rfl, Nat.shiftRight_eq_div_pow]
    rw [show (0x7fffffff : UInt64).toNat = 2 ^ 31 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have hsh : (((w >>> 32) &&& 0x7fffffff) <<< 32).toNat =
      2 ^ 32 * (w.toNat / 2 ^ 32 % 2 ^ 31) := by
    rw [UInt64.toNat_shiftLeft, hix, show (32 : UInt64).toNat % 64 = 32 from rfl,
      Nat.shiftLeft_eq, mul_comm _ (2 ^ 32)]
    apply Nat.mod_eq_of_lt
    omega
  rw [UInt64.toNat_or, hsh, hl, ← Nat.two_pow_add_eq_or_of_lt (by omega)]
  omega

theorem abs_word (x : Float) :
    Float.ofBits ((ixOf x <<< 32) ||| (x.toBits &&& 0xFFFFFFFF)) = x.abs := by
  rw [← F64Bits.ofBits_toBits x.abs]
  congr 1
  apply UInt64.toNat_inj.mp
  rw [ixOf, abs_word_nat, F64Bits.toBits_abs, F64UpperWord.abs_toNat]

theorem atanh_main_eq (x : Float)
    (h0 : ¬ (ixOf x ||| (((x.toBits &&& 0xFFFFFFFF) |||
      ((0 - (x.toBits &&& 0xFFFFFFFF)) &&& 0xFFFFFFFF)) >>> 31)) > 0x3ff00000)
    (h1 : (ixOf x == 0x3ff00000) = false) (h2 : ¬ ixOf x < 0x3e300000) :
    Asinh.atanh x = if x.toBits >>> 32 >>> 31 == 0 then atanhT x else -atanhT x := by
  have h3 := abs_word x
  unfold ixOf at h0 h1 h2 h3
  simp only [Asinh.atanh, h0, h1, h2, h3, ite_false, decide_false, Bool.false_and,
    Bool.false_eq_true]
  rfl

#print axioms abs_word
#print axioms atanh_main_eq

end Library.Numerics.Float64.Asinh.AtanhTheoremBranches
