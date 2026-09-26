import Project.Gpt2RowInvStd.Error
import Project.ProofKit.F32SqrtError

set_option exponentiation.threshold 512

namespace Project.Gpt2RowInvStd.DenominatorError
open Project.ProofKit CodeLib.IEEE32

def variance (total : UInt32) : UInt32 := LeanExe.Float32.divBits total 0x44400000
def shifted (total : UInt32) : UInt32 := LeanExe.Float32.addBits (variance total) 0x3727C5AC
def denominator (total : UInt32) : UInt32 := LeanExe.Float32.sqrtBits (shifted total)
def inverse (total : UInt32) : UInt32 := LeanExe.Float32.divBits 0x3F800000 (denominator total)

theorem epsilon_finite : CodeLib.IEEE32.Finite 0x3727C5AC := by
  change Wasm.IEEE32.isFinite 0x3727C5AC = true
  decide

theorem epsilon_positive : 0 < value 0x3727C5AC := by
  norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
    Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]

theorem one_finite : CodeLib.IEEE32.Finite 0x3F800000 := by
  change Wasm.IEEE32.isFinite 0x3F800000 = true
  decide

theorem one_value : value 0x3F800000 = 1 := by
  norm_num [value, Wasm.IEEE32.scaledValue, Wasm.IEEE32.scaledMagnitude,
    Wasm.IEEE32.sign, Wasm.IEEE32.exponent, Wasm.IEEE32.fraction, UInt32.toNat_ofNat]

structure Ranges (total : UInt32) (divBound addBound sqrtBound reciprocalBound : Nat) : Prop where
  divLower : 24 ≤ divBound
  divUpper : divBound ≤ 275
  divRange : Wasm.IEEE32.scaledMagnitude total * 2 ^ 149 ≤
    Wasm.IEEE32.scaledMagnitude 0x44400000 * 2 ^ divBound
  addUpper : addBound ≤ 276
  addRange : (Wasm.IEEE32.scaledValue (variance total) + Wasm.IEEE32.scaledValue 0x3727C5AC).natAbs < 2 ^ addBound
  sqrtLower : 24 ≤ sqrtBound
  sqrtUpper : sqrtBound ≤ 274
  sqrtRange : Wasm.IEEE32.scaledMagnitude (shifted total) * 2 ^ 149 ≤ 2 ^ (2 * sqrtBound)
  sqrtSign : Wasm.IEEE32.sign (shifted total) = false
  reciprocalLower : 24 ≤ reciprocalBound
  reciprocalUpper : reciprocalBound ≤ 275
  denominatorNonzero : Wasm.IEEE32.scaledMagnitude (denominator total) ≠ 0
  reciprocalRange : Wasm.IEEE32.scaledMagnitude 0x3F800000 * 2 ^ 149 ≤
    Wasm.IEEE32.scaledMagnitude (denominator total) * 2 ^ reciprocalBound

noncomputable def referenceRoot (reference : ℝ) : ℝ := Real.sqrt (reference / 768 + value 0x3727C5AC)

noncomputable def rootError (totalError rootLower : ℝ) (divBound addBound sqrtBound : Nat) : ℝ :=
  F32SqrtBounds.epsilon sqrtBound +
    (F32AdditionBounds.epsilon addBound + (F32DivisionBounds.epsilon divBound + totalError / 768)) / rootLower

noncomputable def inverseError (reference totalError rootLower denominatorLower : ℝ)
    (divBound addBound sqrtBound reciprocalBound : Nat) : ℝ :=
  F32DivisionBounds.epsilon reciprocalBound +
    |1 / referenceRoot reference| * rootError totalError rootLower divBound addBound sqrtBound / denominatorLower

theorem inverse_error (total : UInt32) (reference totalError rootLower denominatorLower : ℝ)
    (divBound addBound sqrtBound reciprocalBound : Nat)
    (hFinite : CodeLib.IEEE32.Finite total) (hReference : 0 ≤ reference)
    (hError : |value total - reference| ≤ totalError)
    (hRanges : Ranges total divBound addBound sqrtBound reciprocalBound)
    (hRootPositive : 0 < rootLower)
    (hRootLower : rootLower ≤ Real.sqrt (value (shifted total)) + referenceRoot reference)
    (hDenPositive : 0 < denominatorLower) (hDenLower : denominatorLower ≤ |value (denominator total)|) :
    CodeLib.IEEE32.Finite (inverse total) ∧
      |value (inverse total) - 1 / referenceRoot reference| ≤
        inverseError reference totalError rootLower denominatorLower divBound addBound sqrtBound reciprocalBound := by
  have hDiv := F32ErrorPropagation.div total 0x44400000 reference 768 totalError 0 768 divBound
    hFinite F32AverageError.divisor_finite hRanges.divLower hRanges.divUpper (by decide)
    hRanges.divRange (by norm_num) (by rw [F32AverageError.divisor_value]; norm_num)
    (by norm_num) hError (by rw [F32AverageError.divisor_value]; norm_num)
  simp only [mul_zero, add_zero] at hDiv
  have hAdd := F32ErrorPropagation.add (variance total) 0x3727C5AC (reference / 768) (value 0x3727C5AC)
    (F32DivisionBounds.epsilon divBound + totalError / 768) 0 addBound
    hDiv.1 epsilon_finite hRanges.addUpper hRanges.addRange hDiv.2 (by simp)
  simp only [add_zero] at hAdd
  have hReferencePos : 0 < reference / 768 + value 0x3727C5AC :=
    add_pos_of_nonneg_of_pos (div_nonneg hReference (by norm_num)) epsilon_positive
  have hRoot := F32SqrtError.error (shifted total) (reference / 768 + value 0x3727C5AC)
    (F32AdditionBounds.epsilon addBound + (F32DivisionBounds.epsilon divBound + totalError / 768))
    rootLower sqrtBound hAdd.1 hRanges.sqrtSign hRanges.sqrtLower hRanges.sqrtUpper hRanges.sqrtRange
    hReferencePos.le hRootPositive hRootLower hAdd.2
  have hInverse := F32ErrorPropagation.div 0x3F800000 (denominator total) 1 (referenceRoot reference)
    0 (rootError totalError rootLower divBound addBound sqrtBound) denominatorLower reciprocalBound
    one_finite hRoot.1 hRanges.reciprocalLower hRanges.reciprocalUpper hRanges.denominatorNonzero
    hRanges.reciprocalRange hDenPositive hDenLower (Real.sqrt_pos.mpr hReferencePos).ne'
    (by rw [one_value]; simp) hRoot.2
  simpa only [inverse, inverseError, zero_add] using hInverse

theorem source_inverse (input : ByteArray) (row : Nat) (mean : UInt32) :
    LeanExe.Models.Gpt2.rowInvStd input row mean = inverse (variancePrefix input row mean 768) := by
  rw [rowInvStd_eq]
  simp only [inverse, denominator, shifted, variance, F32Div.div_eq, F32Sqrt.sqrt_eq, F32Add.add_eq]

#print axioms inverse_error
#print axioms source_inverse
end Project.Gpt2RowInvStd.DenominatorError
