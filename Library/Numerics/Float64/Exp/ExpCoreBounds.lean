import Library.Numerics.Float64.Exp.ExpCoreState
import Library.Numerics.Float64.Exp.ExpTableReconstruction

namespace Library.Numerics.Float64.Exp.ExpCoreBounds
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

def core (x : UInt64) : UInt64 :=
  ExpReconstructionBounds.reconstruction (ExpCoreState.scaleBits x)
    (ExpResidualBounds.residual x) (ExpCoreState.tailBits x)

def floatShifted (x : Float) : Float :=
  Float.ofBits 0x40671547652B82FE * x + Float.ofBits 0x4338000000000000

theorem floatShifted_bits (x : Float) :
    (floatShifted x).toBits = ExpCoreState.shiftedBits x.toBits := by
  have hi := ExpReductionBounds.reduction_constants_finite.1
  have hm := ExpIntegerSelection.magic_values.1
  simp [floatShifted, ExpCoreState.shiftedBits, ExpReductionSelection.product,
    ExpIntegerSelection.shifted, F64Bits.toBits_add, F64Bits.toBits_mul,
    F64Bits.toBits_ofBits, not_nan_of_finite hi, not_nan_of_finite hm]

theorem core_bits (x : Float)
    (hsf : Finite (ExpCoreState.scaleBits x.toBits))
    (htf : Finite (ExpCoreState.tailBits x.toBits)) :
    (Exp.expCore Exp.expTable x false).toBits = core x.toBits := by
  have hd : Exp.expCore Exp.expTable x false =
      ExpReconstructionBounds.floatReconstruction
        (Float.ofBits (ExpScaleBits.scaleBits (floatShifted x).toBits))
        (ExpResidualBounds.floatResidual x)
        (Float.ofBits Exp.expTable[(ExpScaleBits.index (floatShifted x).toBits).toNat]!) := by
    rfl
  rw [hd, ExpReconstructionBounds.reconstruction_bits, floatShifted_bits,
    ExpResidualBounds.residual_bits]
  change ExpReconstructionBounds.reconstruction
    (Float.ofBits (ExpCoreState.scaleBits x.toBits)).toBits
    (ExpResidualBounds.residual x.toBits)
    (Float.ofBits (ExpCoreState.tailBits x.toBits)).toBits = core x.toBits
  simp only [F64Bits.toBits_ofBits, not_nan_of_finite hsf, not_nan_of_finite htf,
    Bool.false_eq_true, ite_false]
  rfl

theorem core_error (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 512) :
    Finite (core x) ∧
      |value (core x) - Real.exp (value x)| ≤
        (7 / 5) * unitRoundoff64 * value (ExpCoreState.scaleBits x) := by
  obtain ⟨k, q, j, hkv, hk, ht, hsf, hs, hslo, hshi⟩ :=
    ExpCoreState.reduction_state x hxf hx
  dsimp only [core]
  rw [ht]
  exact ExpTableReconstruction.table_reconstruction_error x (ExpCoreState.scaleBits x)
    k q j hxf hx hkv hk hsf hs hslo hshi

theorem expCore_error (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| ≤ 512) :
    Finite (Exp.expCore Exp.expTable x false).toBits ∧
      |value (Exp.expCore Exp.expTable x false).toBits - Real.exp (value x.toBits)| ≤
        (7 / 5) * unitRoundoff64 * value (ExpCoreState.scaleBits x.toBits) := by
  obtain ⟨_, _, j, _, _, ht, hsf, _, _, _⟩ :=
    ExpCoreState.reduction_state x.toBits hxf hx
  have htf : Finite (ExpCoreState.tailBits x.toBits) := by
    rw [ht]
    exact (ExpTableBounds.entry_bounds j).2.1
  rw [core_bits x hsf htf]
  exact core_error x.toBits hxf hx

#print axioms floatShifted_bits
#print axioms core_bits
#print axioms core_error
#print axioms expCore_error

end Library.Numerics.Float64.Exp.ExpCoreBounds
