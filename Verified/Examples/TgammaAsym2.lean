import Verified.Examples.TgammaPolyLip
import Verified.Examples.TgammaMul
import Verified.Examples.TgammaApprox
import Verified.Examples.TgammaWords
import Verified.Examples.TgammaSmall
import Verified.Examples.TgammaPolyDDD

/-!
The two series of `Tgamma.asLgammaAsym` in `u = z2h ≈ 1/x²`.  Above `11.5` the code computes
`(c2 + c3) + u (c4 + u (c6 + ⋯))` (`asym_hi`); at or below `11.5` it computes
`(c18 + c19) + z2 ((c20 + c21) + u Q(u))` with the double-double `z2 = z2h + z2l` (`asym_lo`).
The tails in plain double arithmetic get their bounds from `TgammaExpr`, and `eval_hi` and
`eval_lo` identify the exact values with the polynomials of `TgammaApprox.stirHi` and `stirLo`.
-/

namespace Verified.Examples.TgammaAsym2
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaExpr TgammaWords
  TgammaPolyDDD TgammaPolyLip

set_option exponentiation.threshold 4096

def aw (i : ℕ) : UInt64 := asymTable[i]!

theorem aw_finite : ∀ k < 42, Wasm.IEEE64.isFinite asymTable[k]! = true := by decide +kernel

def pairE (a b : ℕ) : FE := .add (.const (aw a)) (.mul .var (.const (aw b)))
def u2E : FE := .mul .var .var
def u4E : FE := .mul u2E u2E

/-- `u (q0 + x2 (q2 + x2 q4))` of the branch above `11.5`. -/
def hiE : FE := .mul .var (.add (pairE 4 6) (.mul u2E (.add (pairE 8 10) (.mul u2E (pairE 12 14)))))

/-- `u ((q0 + x2 q2) + x4 (q4 + x2 (q6 + x2 q8)))` of the branch at or below `11.5`. -/
def loE : FE :=
  .mul .var (.add (.add (pairE 22 24) (.mul u2E (pairE 26 28)))
    (.mul u4E (.add (pairE 30 32) (.mul u2E (.add (pairE 34 36) (.mul u2E (pairE 38 40)))))))

def Uhi : ℚ := 1 / 128
def Ulo : ℚ := 1 / 15

theorem hiE_ok : ok hiE Uhi = true := by decide +kernel
theorem hiE_err : (bnd hiE Uhi).2 ≤ 1 / 2 ^ 66 := by decide +kernel
theorem hiE_mag : (bnd hiE Uhi).1 ≤ 1 / 2 ^ 15 := by decide +kernel
theorem loE_ok : ok loE Ulo = true := by decide +kernel
theorem loE_err : (bnd loE Ulo).2 ≤ 1 / 2 ^ 65 := by decide +kernel
theorem loE_mag : (bnd loE Ulo).1 ≤ 1 / 2 ^ 14 := by decide +kernel

/-- The list of `stirHi`'s series in `1/x²`. -/
def Fhi : List ℚ :=
  (TgammaApprox.q asymTable 2 + TgammaApprox.q asymTable 3) :: TgammaApprox.coeffs asymTable 4 2 6

/-- `u Q(u)` of `stirLo`'s series. -/
def Glo : List ℚ := 0 :: TgammaApprox.coeffs asymTable 22 2 10

theorem eval_hi (u : ℝ) :
    PolyBound.eval Fhi u = ((TgammaApprox.q asymTable 2 + TgammaApprox.q asymTable 3 : ℚ) : ℝ) +
      evalR hiE u := by
  rw [Fhi, PolyBound.eval, eval_coeffs]
  simp only [evalR, hiE, pairE, u2E, aw, TgammaApprox.q, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, zero_add, pow_zero, pow_one, mul_one]
  ring

theorem eval_lo (u : ℝ) : PolyBound.eval Glo u = evalR loE u := by
  rw [Glo, PolyBound.eval, eval_coeffs]
  simp only [evalR, loE, pairE, u2E, u4E, aw, TgammaApprox.q, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.reduceMul, Nat.reduceAdd, zero_add, pow_zero, pow_one, mul_one]
  push_cast
  ring

theorem stirLo_eval (w : ℝ) :
    PolyBound.eval ((TgammaApprox.q asymTable 18 + TgammaApprox.q asymTable 19) ::
      (TgammaApprox.q asymTable 20 + TgammaApprox.q asymTable 21) ::
      TgammaApprox.coeffs asymTable 22 2 10) w =
    ((TgammaApprox.q asymTable 18 + TgammaApprox.q asymTable 19 : ℚ) : ℝ) +
      w * (((TgammaApprox.q asymTable 20 + TgammaApprox.q asymTable 21 : ℚ) : ℝ) +
        PolyBound.eval Glo w) := by
  rw [Glo]
  simp only [PolyBound.eval]
  push_cast
  ring

theorem lip_hi : lipQ Uhi Fhi ≤ 1 / 340 := by decide +kernel
theorem bnd_hi : bndQ Uhi Fhi ≤ 1 / 11 := by decide +kernel
theorem lip_lo : lipQ Ulo Glo ≤ 1 / 1024 := by decide +kernel
theorem bnd_lo : bndQ Ulo Glo ≤ 1 / 2 ^ 14 := by decide +kernel

theorem av (k : ℕ) (hk : k < 42) :
    value (Float.ofBits asymTable[k]!).toBits = (PolyBound.ratOfWord asymTable[k]! : ℝ) :=
  ofBits_value _ (aw_finite k hk)

theorem af (k : ℕ) (hk : k < 42) : Finite (Float.ofBits asymTable[k]!).toBits :=
  ofBits_finite _ (aw_finite k hk)

theorem ev (i : UInt64) (k : ℕ) (h : i.toNat = k) (hk : k < 42) :
    value (entry asymTable i).toBits = (PolyBound.ratOfWord asymTable[k]! : ℝ) := by
  rw [entry_eq _ _ k h]; exact av k hk

theorem ef (i : UInt64) (k : ℕ) (h : i.toNat = k) (hk : k < 42) :
    Finite (entry asymTable i).toBits := by
  rw [entry_eq _ _ k h]; exact af k hk

theorem cbounds :
    (1 / 13 : ℚ) ≤ PolyBound.ratOfWord asymTable[2]! ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[3]!) ≤ 1 / 2 ^ 57 ∧
    (1 / 13 : ℚ) ≤ PolyBound.ratOfWord asymTable[18]! ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[19]!) ≤ 1 / 2 ^ 57 ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[20]!) ≤ 1 / 256 ∧
    (1 / 512 : ℚ) ≤ PolyBound.qabs (PolyBound.ratOfWord asymTable[20]!) ∧
    PolyBound.qabs (PolyBound.ratOfWord asymTable[21]!) ≤ 1 / 2 ^ 62 ∧
    PolyBound.ratOfWord asymTable[2]! ≤ 1 / 11 ∧ PolyBound.ratOfWord asymTable[18]! ≤ 1 / 11 := by
  decide +kernel

#print axioms hiE_err
#print axioms loE_err
#print axioms eval_hi
#print axioms eval_lo
#print axioms lip_hi
#print axioms lip_lo

end Verified.Examples.TgammaAsym2
