import Verified.Examples.LgammaLogAccKern
import Verified.Examples.LgammaLogAccRed
import Verified.Examples.TgammaAcc2
import Verified.Examples.TgammaLogdKernel

/-!
The tail of `Lgamma.asLogdAccurate` after the reduction `Lgamma.logReduce`: the kernel `X · logAccPoly X` of `LgammaLogAccKern`, the sums of the table's
triples `h1 i1 + h2 i2` for `-log r`, the products of the exponent `ed` by the three parts of
`ln 2`, and the renormalization.  The high parts of the table and `ln 2` lie on the grid `2^-42`,
the middle parts on `2^-94`, and the middle part of `ln 2` on `2^-84`, so the products by `ed`,
`|ed| ≤ 1074`, and the sums of high and middle parts are exact.
-/

namespace Verified.Examples.LgammaLogAccTail
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul LgammaLogAccKern

set_option exponentiation.threshold 4096

/-! ### The words of the table -/

/-- The integer numerators of the table's high parts on `2^-42` and middle parts on `2^-94`. -/
def hiN (i : ℕ) : ℤ := (PolyBound.ratOfWord H[i]! * 2 ^ 42).num
def midN (i : ℕ) : ℤ := (PolyBound.ratOfWord H[i]! * 2 ^ 94).num

theorem words_ok :
    (∀ i < 216, Wasm.IEEE64.isFinite H[i]! = true) ∧
    (∀ i < 33, PolyBound.ratOfWord H[3 * i + 2]! = hiN (3 * i + 2) / 2 ^ 42 ∧
      0 ≤ hiN (3 * i + 2) ∧ hiN (3 * i + 2) ≤ 3048493539143) ∧
    (∀ i < 32, PolyBound.ratOfWord H[99 + 3 * i + 2]! = hiN (99 + 3 * i + 2) / 2 ^ 42 ∧
      0 ≤ hiN (99 + 3 * i + 2) ∧ hiN (99 + 3 * i + 2) ≤ 2 ^ 37) ∧
    (∀ i < 33, PolyBound.ratOfWord H[3 * i + 1]! = midN (3 * i + 1) / 2 ^ 94 ∧
      0 ≤ midN (3 * i + 1) ∧ midN (3 * i + 1) ≤ 4312648921537145) ∧
    (∀ i < 32, PolyBound.ratOfWord H[99 + 3 * i + 1]! = midN (99 + 3 * i + 1) / 2 ^ 94 ∧
      0 ≤ midN (99 + 3 * i + 1) ∧ midN (99 + 3 * i + 1) ≤ 4496283226037544) ∧
    (∀ i < 33, 0 ≤ PolyBound.ratOfWord H[3 * i]! ∧ PolyBound.ratOfWord H[3 * i]! ≤ 1 / 2 ^ 93) ∧
    (∀ i < 32, 0 ≤ PolyBound.ratOfWord H[99 + 3 * i]! ∧
      PolyBound.ratOfWord H[99 + 3 * i]! ≤ 1 / 2 ^ 93) := by
  decide +kernel

theorem ln2_words :
    PolyBound.ratOfWord 0x3FE62E42FEFA3800 = 3048493539143 / 2 ^ 42 ∧
      PolyBound.ratOfWord 0x3D2EF35793C76000 = 1063452974651 / 2 ^ 84 ∧
      0 < PolyBound.ratOfWord 0x3A8CC01F97B57A08 ∧
      PolyBound.ratOfWord 0x3A8CC01F97B57A08 ≤ 1 / 2 ^ 86 ∧
      Wasm.IEEE64.isFinite 0x3FE62E42FEFA3800 = true ∧
      Wasm.IEEE64.isFinite 0x3D2EF35793C76000 = true ∧
      Wasm.IEEE64.isFinite 0x3A8CC01F97B57A08 = true := by
  decide +kernel

/-- The indices of the table's triples as words. -/
theorem ix_a (i : UInt64) (hi : i.toNat < 33) :
    (3 * i).toNat = 3 * i.toNat ∧ (3 * i + 1).toNat = 3 * i.toNat + 1 ∧
      (3 * i + 2).toNat = 3 * i.toNat + 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat] <;> omega

theorem ix_b (i : UInt64) (hi : i.toNat < 32) :
    (99 + 3 * i).toNat = 99 + 3 * i.toNat ∧ (99 + 3 * i + 1).toNat = 99 + 3 * i.toNat + 1 ∧
      (99 + 3 * i + 2).toNat = 99 + 3 * i.toNat + 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.reduceToNat] <;> omega

theorem entry_val (k : ℕ) (hk : k < 216) (i : UInt64) (hi : i.toNat = k) :
    Finite (entry H i).toBits ∧ value (entry H i).toBits = (PolyBound.ratOfWord H[k]! : ℝ) := by
  have hw := words_ok.1 k hk
  have he : entry H i = Float.ofBits H[k]! := by unfold Tgamma.entry; rw [hi]
  rw [he]
  exact ⟨TgammaWords.ofBits_finite _ hw, TgammaWords.ofBits_value _ hw⟩

end Verified.Examples.LgammaLogAccTail
