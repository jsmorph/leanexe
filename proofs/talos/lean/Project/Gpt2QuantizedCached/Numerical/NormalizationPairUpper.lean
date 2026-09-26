import Project.Gpt2QuantizedCached.Numerical.NormalizationUpperSound
import Project.Gpt2QuantizedCached.Numerical.NormalizationRange
import Project.Gpt2QuantizedCached.Numerical.TensorBounds

namespace Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
open LeanExe.Models.Gpt2 Project.ProofKit

noncomputable def pairParameters (d : PairData) : Norm.Parameters :=
  ⟨NormalizationRange.parameters d.quantized, NormalizationRange.parameters d.reference⟩

structure Magnitudes (qw qi rw ri : ByteArray) (qs rs : Nat) (d : PairData) : Prop where
  quantizedCenter : ∀ i < 768,
    |CodeLib.IEEE32.value (Gpt2CachedStep.LayerNorm.Numerical.centered qi i)| ≤ DyadicUpper.value d.quantizedCenter
  referenceCenter : ∀ i < 768,
    |CodeLib.IEEE32.value (Gpt2CachedStep.LayerNorm.Numerical.centered ri i)| ≤ DyadicUpper.value d.referenceCenter
  realCenter : ∀ i < 768,
    |CodeLib.IEEE32.value (word ri i) - Gpt2CachedStep.LayerNorm.ForwardError.referenceMean (fun j => CodeLib.IEEE32.value (word ri j))| ≤ DyadicUpper.value d.realCenter
  quantizedGain : ∀ i < 768, |CodeLib.IEEE32.value (word qw (qs + i))| ≤ DyadicUpper.value d.gain
  referenceGain : ∀ i < 768, |CodeLib.IEEE32.value (word rw (rs + i))| ≤ DyadicUpper.value d.gain

theorem pair_close (qw qi rw ri : ByteArray) (qs qb rs rb E : Nat) (d : PairData)
    (h : Norm.Ranges qw qi rw ri qs qb rs rb (pairParameters d)) (hm : Magnitudes qw qi rw ri qs rs d)
    (he : Close qi ri 768 (DyadicUpper.value E)) :
    Close (layerNorm qw qi qs qb 1) (layerNorm rw ri rs rb 1) 768 (DyadicUpper.value (pair d E)) := by
  intro i hi
  have hq := component_sound qw qi qs (fun j => CodeLib.IEEE32.value (word ri j)) (fun _ => DyadicUpper.value E)
    d.quantized E d.quantizedCenter d.realCenter d.gain (fun _ _ => DyadicUpper.nonnegative E)
    (fun _ _ => le_rfl) hm.quantizedCenter hm.realCenter hm.quantizedGain i hi
  have hr := component_sound rw ri rs (fun j => CodeLib.IEEE32.value (word ri j)) (fun _ => 0)
    d.reference 0 d.referenceCenter d.realCenter d.gain (fun _ _ => le_rfl)
    (fun _ _ => DyadicUpper.nonnegative 0) hm.referenceCenter hm.realCenter hm.referenceGain i hi
  have hp := LayerNormPair.component_error qw qi rw ri qs qb rs rb (fun _ => DyadicUpper.value E)
    (NormalizationRange.parameters d.quantized) (NormalizationRange.parameters d.reference)
    h.quantized h.reference he h.scaleEqual h.biasEqual i hi
  exact hp.2.2.trans (DyadicUpper.add_bound _ _ _ _ hq hr)

#print axioms pair_close
end Project.Gpt2QuantizedCached.Numerical.NormalizationUpper
