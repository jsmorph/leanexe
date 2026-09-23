import Project.Gpt2QuantizedCached.ModelScan

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Model
open LeanExe.Models.Gpt2.Quantized

def globalValid (weights : ByteArray) : Bool :=
  validCoefficients weights tokenWeightOffset (50257 * 768) &&
    validScales weights tokenScaleOffset 50257 &&
    finiteWords weights positionOffset (1024 * 768) &&
    finiteWords weights finalNormOffset 1536

def blocksValid (weights : ByteArray) : Bool :=
  (List.range 12).all fun layer => validBlock weights (blocksOffset + layer * blockBytes)

theorem validateModel_eq (weights : ByteArray) :
    validateModel weights =
      if validHeader weights then
        if globalValid weights && blocksValid weights then 0 else 2
      else 1 := by
  have hGlobal : (!validCoefficients weights tokenWeightOffset (50257 * 768) ||
      !validScales weights tokenScaleOffset 50257 ||
      !finiteWords weights positionOffset (1024 * 768) ||
      !finiteWords weights finalNormOffset 1536) = !globalValid weights := by
    simp [globalValid, Bool.not_and, Bool.or_assoc]
  simp only [validateModel, hGlobal,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, ← List.range_eq_range']
  have hScan := blockScan_eq weights (List.range 12)
  simp only [blockScan, Project.ProofKit.ListValidation.scan] at hScan
  rw [hScan]
  cases hHeaderChoice : validHeader weights <;>
    cases hGlobalChoice : globalValid weights <;>
    cases hBlocksChoice : blocksValid weights
  all_goals
    simp only [blocksValid] at hBlocksChoice
    simp [blocksValid, hHeaderChoice, hGlobalChoice, hBlocksChoice]
  all_goals rfl

theorem validateModel_zero_iff (weights : ByteArray) :
    validateModel weights = 0 ↔ Validated weights := by
  rw [validateModel_eq]
  constructor
  · intro h
    have hHeader : validHeader weights = true := by
      cases hh : validHeader weights <;> simp_all
    have hAll : (globalValid weights && blocksValid weights) = true := by
      cases hh : globalValid weights && blocksValid weights <;> simp_all
    simp only [globalValid, blocksValid, Bool.and_eq_true,
      List.all_eq_true, List.mem_range, validBlock_iff] at hAll
    exact ⟨hHeader, hAll.1.1.1.1, hAll.1.1.1.2, hAll.1.1.2,
      hAll.1.2, hAll.2⟩
  · intro h
    have hAll : (globalValid weights && blocksValid weights) = true := by
      simp only [globalValid, blocksValid, Bool.and_eq_true,
        List.all_eq_true, List.mem_range, validBlock_iff]
      exact ⟨⟨⟨⟨h.tokenCoefficients, h.tokenScales⟩, h.positions⟩,
        h.finalNormalization⟩, h.blocks⟩
    simp [h.header, hAll]

#print axioms blockScan_eq
#print axioms validateModel_eq
#print axioms validateModel_zero_iff
end Project.Gpt2QuantizedCached.Model
