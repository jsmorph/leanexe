import Project.Gpt2QuantizedCached.GroupedProjection.ProjectionGroupFinish

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.GroupedProjection.Projection
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem group_parts (withBias : Bool) :
    groupStep withBias = dotPrefix withBias ++ scaleCode withBias ++ finishGroup withBias := by
  cases withBias <;> rfl

theorem group_spec (env : HostEnv Unit) (initial : Store Unit)
    (weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr outputPtr : UInt64) (weights input : ByteArray)
    (weightOffset scaleOffset biasOffset width outputWidth rows index group : Nat)
    (withBias : Bool) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem weightsPtr.toNat weights)
    (hValues : ByteArrayAt initial.mem valuePtr.toNat (quantizeRows input 64 (rows * (width / 64))).values)
    (hScales : ByteArrayAt initial.mem scalePtr.toNat (quantizeRows input 64 (rows * (width / 64))).scales)
    (hWeightSize : weightOffset + width * outputWidth ≤ weights.size)
    (hScaleSize : scaleOffset + outputWidth * 4 ≤ weights.size)
    (hWidth : 0 < width) (hMultiple : 64 ∣ width) (hCount : rows * outputWidth < UInt64.size)
    (hIndex : index < rows * outputWidth) (hGroup : group < width / 64)
    (hReady : PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) index outputPtr frame)
    (hGroupReady : RangeFoldLoop.Ready 97 98 (width / 64) group frame)
    (hAcc : Accumulator weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
      biasOffset width outputWidth rows index group withBias frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ result, PackedGenerateLoop.Ready 32 95 96 (rows * outputWidth) index outputPtr result →
      RangeFoldLoop.Ready 97 98 (width / 64) (group + 1) result →
      Accumulator weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr weights input weightOffset scaleOffset
        biasOffset width outputWidth rows index (group + 1) withBias result →
      wp «module» rest Q initial { result with values :=
        [.i32 (PackedGenerateLoop.address outputPtr index)] } env) :
    wp «module» (groupStep withBias ++ rest) Q initial
      { frame with values := [.i32 (PackedGenerateLoop.address outputPtr index)] } env := by
  rw [group_parts, List.append_assoc, List.append_assoc]
  apply dotPrefix_spec env initial weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr outputPtr weights input
    weightOffset scaleOffset biasOffset width outputWidth rows index group withBias frame
    hWeights hValues hWeightSize hWidth hMultiple hCount hIndex hGroup hReady hGroupReady hAcc
  intro afterDot hReadyDot hGroupDot hStateDot
  apply scaleCode_spec env initial weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr outputPtr weights input
    weightOffset scaleOffset biasOffset width outputWidth rows index group withBias _ afterDot
    hWeights hScales hScaleSize hCount hIndex hGroup hReadyDot hGroupDot hStateDot
  intro afterScale hReadyScale hGroupScale hStateScale
  apply finishGroup_spec env initial weightsOwner weightsPtr inputOwner inputPtr valuePtr scalePtr outputPtr weights input
    weightOffset scaleOffset biasOffset width outputWidth rows index group withBias afterScale
    (by
      have hRows : 0 < rows := by nlinarith
      have := hScales.1
      rw [grouped_scales_size] at this
      change _ < 18446744073709551616
      nlinarith) hGroup hReadyScale hGroupScale hStateScale
  exact hNext

#print axioms group_spec

end Project.Gpt2QuantizedCached.GroupedProjection.Projection
