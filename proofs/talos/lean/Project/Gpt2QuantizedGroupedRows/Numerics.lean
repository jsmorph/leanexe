import Project.Gpt2QuantizedGroupedRows.Source
import Project.ProofKit.F32IntegerExact

namespace Project.Gpt2QuantizedGroupedRows
open LeanExe.Models.Gpt2.Quantized LeanExe.Signed32 Project.ProofKit

theorem group_integer_conversion_exact (weights values : ByteArray)
    (weightOffset inputOffset count : Nat) (hc : count ≤ 64)
    (inputValid : ∀ i < count, values[inputOffset + i]! ≠ 128)
    (weightsValid : ∀ i < count, weights[weightOffset + i]! ≠ 128) :
    let accumulator := dot weights values weightOffset inputOffset count
    CodeLib.IEEE32.Finite (LeanExe.Float32.ofInt32Bits accumulator) ∧
      CodeLib.IEEE32.value (LeanExe.Float32.ofInt32Bits accumulator) = decode accumulator := by
  have h := group_accumulator_bound weights values weightOffset inputOffset count hc inputValid weightsValid
  have hNat : (decode (dot weights values weightOffset inputOffset count)).natAbs ≤ 1032256 := by
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  exact F32IntegerExact.conversion_exact _ (by omega)

#print axioms group_integer_conversion_exact
end Project.Gpt2QuantizedGroupedRows
