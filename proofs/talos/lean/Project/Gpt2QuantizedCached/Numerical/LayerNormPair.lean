import Project.Gpt2CachedStep.LayerNorm.ForwardError
import Project.ProofKit.F32ErrorPropagation

namespace Project.Gpt2QuantizedCached.Numerical.LayerNormPair
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

structure Parameters where
  bounds : Project.Gpt2CachedStep.LayerNorm.ForwardError.Bounds
  rootLower : ℝ
  denominatorLower : ℝ

structure Ranges (weights input : ByteArray) (scaleOffset biasOffset : Nat) (X : Nat → ℝ) (p : Parameters) : Prop where
  arithmetic : Project.Gpt2CachedStep.LayerNorm.ForwardError.Ranges weights input scaleOffset biasOffset p.bounds
  rootPositive : 0 < p.rootLower
  rootLower : p.rootLower ≤ Real.sqrt (value (Project.Gpt2RowInvStd.DenominatorError.shifted
    (Project.Gpt2RowInvStd.variancePrefix input 0 (rowMean input 0) 768))) + Project.Gpt2RowInvStd.DenominatorError.referenceRoot (Project.Gpt2CachedStep.LayerNorm.ForwardError.referenceSquares X)
  denominatorPositive : 0 < p.denominatorLower
  denominatorLower : p.denominatorLower ≤ |value (Project.Gpt2RowInvStd.DenominatorError.denominator
    (Project.Gpt2RowInvStd.variancePrefix input 0 (rowMean input 0) 768))|

noncomputable def error (qw qinput rweights rinput : ByteArray) (qScale rScale : Nat)
    (inputError : Nat → ℝ) (qp rp : Parameters) (i : Nat) : ℝ :=
  Project.Gpt2CachedStep.LayerNorm.ForwardError.componentError qw qinput qScale (fun j => value (word rinput j)) inputError qp.bounds qp.rootLower qp.denominatorLower i +
    Project.Gpt2CachedStep.LayerNorm.ForwardError.componentError rweights rinput rScale (fun j => value (word rinput j)) (fun _ => 0) rp.bounds rp.rootLower rp.denominatorLower i

theorem component_error (qw qinput rw rinput : ByteArray) (qScale qBias rScale rBias : Nat)
    (inputError : Nat → ℝ) (qp rp : Parameters)
    (hq : Ranges qw qinput qScale qBias (fun j => value (word rinput j)) qp)
    (hr : Ranges rw rinput rScale rBias (fun j => value (word rinput j)) rp)
    (hInput : ∀ j < 768, |value (word qinput j) - value (word rinput j)| ≤ inputError j)
    (hScale : ∀ j < 768, word qw (qScale + j) = word rw (rScale + j))
    (hBias : ∀ j < 768, word qw (qBias + j) = word rw (rBias + j))
    (i : Nat) (hi : i < 768) :
    CodeLib.IEEE32.Finite (word (layerNorm qw qinput qScale qBias 1) i) ∧
      CodeLib.IEEE32.Finite (word (layerNorm rw rinput rScale rBias 1) i) ∧
      |value (word (layerNorm qw qinput qScale qBias 1) i) - value (word (layerNorm rw rinput rScale rBias 1) i)| ≤
        error qw qinput rw rinput qScale rScale inputError qp rp i := by
  have hqe := Project.Gpt2CachedStep.LayerNorm.ForwardError.component_error qw qinput qScale qBias (fun j => value (word rinput j)) inputError
    qp.bounds qp.rootLower qp.denominatorLower hq.arithmetic hInput hq.rootPositive hq.rootLower
    hq.denominatorPositive hq.denominatorLower i hi
  have hre := Project.Gpt2CachedStep.LayerNorm.ForwardError.component_error rw rinput rScale rBias (fun j => value (word rinput j)) (fun _ => 0)
    rp.bounds rp.rootLower rp.denominatorLower hr.arithmetic (by intro j hj; simp) hr.rootPositive hr.rootLower
    hr.denominatorPositive hr.denominatorLower i hi
  rw [hScale i hi, hBias i hi] at hqe
  exact ⟨hqe.1, hre.1, F32ErrorPropagation.compare _ _ _ _ _ hqe.2 hre.2⟩

#print axioms component_error
end Project.Gpt2QuantizedCached.Numerical.LayerNormPair
