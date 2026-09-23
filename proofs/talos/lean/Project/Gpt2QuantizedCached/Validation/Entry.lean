import Project.Gpt2QuantizedCached.Validation.Blocks
import Project.Gpt2QuantizedCached.Header

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

private theorem entry_code : func28 = func28.take 10 ++ ReadOnlyDisjunction.negateProgram ++
    ReadOnlyDisjunction.canonicalProgram ++
    [.iff 0 0 [.constI64 1, .localSet 51] globalCode, .localGet 51] := rfl

private theorem global_code : globalCode = globalCode.take 39 ++
    [.iff 0 0 [.constI64 2, .localSet 51] blocksCode] := rfl

theorem exact (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray)
    (hWeights : PackedMemory.ByteArrayAt initial.mem ptr.toNat weights) :
    TerminatesWith env «module» 28 initial
      [.i64 (UInt64.ofNat weights.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (validateModel weights)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func28Def) rfl ?_
  change wp «module» func28 _ initial
    { params := parameters owner ptr weights, locals := List.replicate 62 (.i64 0) } env
  rw [entry_code]
  simp only [List.append_assoc, func28, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [parameters]
  refine wp_call_tw (Header.exact env initial owner ptr weights hWeights) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  apply ReadOnlyDisjunction.negate_spec _ _ _ _ _ rfl
  apply ReadOnlyDisjunction.canonical_spec _ _ _ _ _ rfl
  simp only [List.cons_append, List.nil_append, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  cases hHeader : validHeader weights
  · rw [ite_eq_left (by decide)]
    wp_packed_frame [parameters]
    simp [func28Def, Model.validateModel_eq, hHeader]
  · rw [ite_eq_right (by decide)]
    have hSize := Model.size_of_header weights hHeader
    rw [global_code]
    simp only [List.append_assoc]
    apply global_spec env initial owner ptr weights hWeights hSize _ rfl rfl rfl
    intro checked hParams hLength hValues
    refine wp_iff_cons hValues ?_
    cases hGlobal : Model.globalValid weights
    · rw [ite_eq_left (by simp [hGlobal])]
      wp_packed_frame [parameters, hParams, hLength]
      simp [func28Def, Model.validateModel_eq, hHeader, hGlobal]
    · rw [ite_eq_right (by simp [hGlobal])]
      apply blocks_spec env initial owner ptr weights hWeights hSize
        { checked with values := [] } hParams hLength rfl
      intro result hResultParams hResultLength hResultValues hStatus
      wp_packed_frame [parameters, hResultParams, hResultLength, hResultValues, hStatus]
      simp [func28Def, Model.validateModel_eq, hHeader, hGlobal]

#print axioms exact
end Project.Gpt2QuantizedCached.Validation
