import Project.Gpt2QuantizedCached.Validation.GlobalChecks

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

private theorem globalCode_split : globalCode.take 39 =
    globalCode.take 25 ++ ReadOnlyDisjunction.negateProgram ++
    ReadOnlyDisjunction.program (globalCheck 0) ++
    ReadOnlyDisjunction.program (globalCheck 1) ++
    ReadOnlyDisjunction.program (globalCheck 2) ++
    ReadOnlyDisjunction.canonicalProgram := by rfl

theorem global_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray)
    (hWeights : PackedMemory.ByteArrayAt initial.mem ptr.toNat weights)
    (hSize : weights.size = modelBytes)
    (frame : Locals) (hParams : frame.params = parameters owner ptr weights)
    (hLength : frame.locals.length = 64) (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Program)
    (hNext : ∀ result, result.params = parameters owner ptr weights →
      result.locals.length = 64 →
      result.values = [.i32 (if !Model.globalValid weights then 1 else 0)] →
      wp «module» rest Q initial result env) :
    wp «module» (globalCode.take 39 ++ rest) Q initial frame env := by
  rw [globalCode_split]
  simp only [List.append_assoc]
  apply coefficients_spec env initial owner ptr weights hWeights hSize frame hParams hLength hValues
  intro first hFirstParams hFirstLength hFirstValues
  apply ReadOnlyDisjunction.negate_spec _ _ _ first _ hFirstValues
  apply ReadOnlyDisjunction.program_spec _ _ _ _ _ _ _ _
    (scales_spec env initial owner ptr weights hWeights hSize)
    { first with values := [.i32 (if !validCoefficients weights tokenWeightOffset (50257 * 768) then 1 else 0)] }
    hFirstParams hFirstLength rfl
  intro second hSecondParams hSecondLength hSecondValues
  apply ReadOnlyDisjunction.program_spec _ _ _ _ _ _ _ _
    (positions_spec env initial owner ptr weights hWeights hSize) _ hSecondParams hSecondLength hSecondValues
  intro third hThirdParams hThirdLength hThirdValues
  apply ReadOnlyDisjunction.program_spec _ _ _ _ _ _ _ _
    (normalization_spec env initial owner ptr weights hWeights hSize) _ hThirdParams hThirdLength hThirdValues
  intro fourth hFourthParams hFourthLength hFourthValues
  apply ReadOnlyDisjunction.canonical_spec _ _ _ fourth _ hFourthValues
  apply hNext fourth hFourthParams hFourthLength
  simpa only [Model.globalValid, Bool.not_and] using hFourthValues

#print axioms global_spec
end Project.Gpt2QuantizedCached.Validation
