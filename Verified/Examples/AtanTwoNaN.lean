import Verified.Examples.AtanTwoBits
import LeanExe.ProofKit.F64Saturate

/-!
`Atan.atan2` at a NaN.  fdlibm's test for a NaN input holds when either input is a NaN
(`nan_test_nan`), and the code then returns `x + y`, which is the canonical NaN in the semantics of
WebAssembly that the compiler's theorems use (`atan2_nan`).  `AtanBytes.atan2_bytes_accuracy`
states that the compiled module returns the bits of `Atan.atan2 y x`, so the theorem holds for the
module as well.
-/

namespace Verified.Examples.AtanTwoNaN
open LeanExe.ProofKit AtanTheoremBranches AtanTwoBranches AtanTwoBits

set_option exponentiation.threshold 4096

/-- fdlibm's NaN test holds for a NaN word. -/
theorem nan_test_nan (x : Float) (hx : Wasm.IEEE64.isNaN x.toBits = true) :
    (ixOf x ||| ((lxOf x ||| ((0 - lxOf x) &&& 0xFFFFFFFF)) >>> 31)) > 0x7ff00000 := by
  have hw := x.toBits.toNat_lt
  have hi := ix_toNat x
  have hl := lx_toNat x
  simp only [Wasm.IEEE64.isNaN, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, Bool.and_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq] at hx
  obtain ⟨he, hf⟩ := hx
  rw [gt_iff_lt, UInt64.lt_iff_toNat_lt, UInt64.toNat_or,
    show (0x7ff00000 : UInt64).toNat = 0x7ff00000 from rfl]
  by_cases h1 : 0x7ff00000 < (ixOf x).toNat
  · exact lt_of_lt_of_le h1 Nat.left_le_or
  · have hix : (ixOf x).toNat = 0x7ff00000 := by omega
    have hl0 : 0 < (lxOf x).toNat := by omega
    have hl1 : (lxOf x).toNat < 2 ^ 32 := by omega
    have ht : (0 - lxOf x).toNat &&& (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - (lxOf x).toNat := by
      rw [show (0xFFFFFFFF : UInt64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
        UInt64.toNat_sub, UInt64.toNat_zero]
      omega
    have hs : ((lxOf x ||| ((0 - lxOf x) &&& 0xFFFFFFFF)) >>> 31).toNat = 1 := by
      rw [UInt64.toNat_shiftRight, UInt64.toNat_or, UInt64.toNat_and, ht,
        show (31 : UInt64).toNat % 64 = 31 from rfl, Nat.shiftRight_eq_div_pow]
      have h2 : 2 ^ 32 - (lxOf x).toNat < 2 ^ 32 := by omega
      have h3 := Nat.or_lt_two_pow hl1 h2
      have h4 : (lxOf x).toNat ≤ (lxOf x).toNat ||| (2 ^ 32 - (lxOf x).toNat) := Nat.left_le_or
      have h5 : 2 ^ 32 - (lxOf x).toNat ≤ (lxOf x).toNat ||| (2 ^ 32 - (lxOf x).toNat) :=
        Nat.right_le_or
      omega
    rw [hix, hs]
    decide

/-- **`atan2` at a NaN**: when either input is a NaN, the result is the canonical NaN. -/
theorem atan2_nan (y x : Float)
    (h : Wasm.IEEE64.isNaN y.toBits = true ∨ Wasm.IEEE64.isNaN x.toBits = true) :
    (Atan.atan2 y x).toBits = Wasm.IEEE64.canonicalNaN := by
  have hg : ((ixOf x ||| ((lxOf x ||| ((0 - lxOf x) &&& 0xFFFFFFFF)) >>> 31)) > 0x7ff00000 ||
      (ixOf y ||| ((lxOf y ||| ((0 - lxOf y) &&& 0xFFFFFFFF)) >>> 31)) > 0x7ff00000) = true := by
    rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    rcases h with hy | hx
    · exact Or.inr (nan_test_nan y hy)
    · exact Or.inl (nan_test_nan x hx)
  unfold ixOf lxOf at hg
  simp only [Atan.atan2, hg, ite_true]
  rw [F64Bits.toBits_add]
  rcases h with hy | hx
  · simp only [Wasm.IEEE64.add, hy, Bool.or_true, ite_true]
  · exact F64Saturate.add_nan_left _ _ hx

#print axioms nan_test_nan
#print axioms atan2_nan

end Verified.Examples.AtanTwoNaN
