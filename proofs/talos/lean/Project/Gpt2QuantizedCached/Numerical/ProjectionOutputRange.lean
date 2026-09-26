import Project.Gpt2QuantizedCached.Numerical.ProjectionQuantizedRange

namespace Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
open LeanExe.Models.Gpt2 Project.ProofKit Gpt2QuantizedGroupedRows
open Gpt2QuantizedGroupedRows.ForwardError

theorem partial_magnitude (weights input : ByteArray)
    (weightOffset scaleOffset width row group scaleBound outputBound : Nat) (X W ex ew : Nat → ℝ)
    (h : GroupRanges weights input weightOffset scaleOffset width 1 0 row group scaleBound outputBound X W ex ew) :
    CodeLib.IEEE32.Finite (partialValue weights input weightOffset scaleOffset width 1 0 row group) ∧
      (Wasm.IEEE32.scaledValue (partialValue weights input weightOffset scaleOffset width 1 0 row group)).natAbs ≤
        F32UniformRange.productMagnitude outputBound := by
  have ha := group_accumulator_bound weights (Quantized.quantizeRows input 64 (1 * (width / 64))).values
    (weightOffset + row * width + group * 64) (0 * width + group * 64) 64 (by decide) h.inputValid h.weightValid
  have hn : (LeanExe.Signed32.decode (accumulator weights input weightOffset width 1 0 row group)).natAbs < 2 ^ 24 := by
    rw [← Int.natCast_natAbs] at ha
    have hm : (LeanExe.Signed32.decode (accumulator weights input weightOffset width 1 0 row group)).natAbs ≤ 1032256 := by exact_mod_cast ha
    omega
  have hc := F32IntegerExact.conversion_exact _ hn
  have hs := F32UniformRange.product_magnitude _ _ scaleBound h.scaleLower h.scaleUpper h.inputFinite h.weightFinite h.scaleRange
  exact F32UniformRange.product_magnitude _ _ outputBound h.outputLower h.outputUpper hc.1 hs.1 h.outputRange

theorem output_ranges (reference quantized input : ByteArray) (l : Layout)
    (w : WeightBounds) (inputMagnitude scaleMagnitude : Nat) (p : Parameters)
    (hw : checkWeights reference quantized l w = true)
    (ha : checkActivations input scaleMagnitude = true)
    (hp : checkRanges l.matrix.inputWidth inputMagnitude scaleMagnitude w p = true)
    (he : Export.check reference quantized = true) (hl : l.matrix ∈ Export.projections)
    (hs : input.size = l.matrix.inputWidth * 4) (row : Nat) (hr : row < l.matrix.outputWidth) :
    OutputError.Ranges quantized input l.matrix.coefficientOffset l.matrix.scaleOffset l.quantizedBias
      l.matrix.inputWidth row l.withBias (fun i => CodeLib.IEEE32.value (word input i))
      (fun i => CodeLib.IEEE32.value (weightWord reference l row i))
      (activationError input l.matrix.inputWidth) (fun _ => weightError quantized l row) (quantizedBounds p) := by
  have hg (group : Nat) (hgt : group < l.matrix.inputWidth / 64) :=
    group_ranges reference quantized input l w inputMagnitude scaleMagnitude p hw ha hp he hl hs row group hr hgt
  have hm (group : Nat) (hgt : group < l.matrix.inputWidth / 64) :=
    partial_magnitude _ _ _ _ _ _ _ _ _ _ _ _ _ (hg group hgt)
  have hw := checked_weights reference quantized l w hw row hr
  simp only [checkRanges, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at hp
  have ht := F32UniformRange.sumFits_sound _ _ _ _ hp.2.2.1
    (fun g hgt => (hm g hgt).1) (fun g hgt => (hm g hgt).2)
  have hb := hp.2.2.1
  simp only [F32UniformRange.sumFits, Bool.and_eq_true, decide_eq_true_eq] at hb
  refine ⟨hg, fun _ _ => hb.1, ht.1, ?_, fun _ => hp.2.2.2.2.1, ?_⟩
  · intro hBias
    have hc := hw.2.2.2.2 hBias
    change CodeLib.IEEE32.Finite (LeanExe.Packed.getUInt32LE! quantized (l.quantizedBias + row * 4))
    rw [← hc.2.2]
    exact hc.1
  · intro hBias
    have hc := hw.2.2.2.2 hBias
    change (Wasm.IEEE32.scaledValue (OutputError.total quantized input l.matrix.coefficientOffset l.matrix.scaleOffset l.matrix.inputWidth row) +
      Wasm.IEEE32.scaledValue (LeanExe.Packed.getUInt32LE! quantized (l.quantizedBias + row * 4))).natAbs < _
    rw [← hc.2.2]
    exact bias_range _ _ _ _ _ ht.2.2 hc.2.1 hp.2.2.2.2.2.2

#print axioms partial_magnitude
#print axioms output_ranges
end Project.Gpt2QuantizedCached.Numerical.ProjectionRangeCertificate
