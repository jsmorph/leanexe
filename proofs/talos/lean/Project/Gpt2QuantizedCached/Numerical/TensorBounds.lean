import Project.Gpt2QuantizedCached.Numerical.LayerNormPair
import Project.Gpt2QuantizedCached.Numerical.ProjectionPair
import Project.Gpt2QuantizedCached.Numerical.AttentionPair
import Project.Gpt2QuantizedCached.Numerical.PointwisePair
import Project.ProofKit.FiniteErrorBound

namespace Project.Gpt2QuantizedCached.Numerical
open LeanExe.Models.Gpt2 Project.ProofKit CodeLib.IEEE32

def Close (q r : ByteArray) (n : Nat) (error : ℝ) : Prop :=
  ∀ i < n, |value (word q i) - value (word r i)| ≤ error

namespace Norm
structure Parameters where
  quantized : LayerNormPair.Parameters
  reference : LayerNormPair.Parameters

structure Ranges (qw qi rw ri : ByteArray) (qs qb rs rb : Nat) (p : Parameters) : Prop where
  quantized : LayerNormPair.Ranges qw qi qs qb (fun i => value (word ri i)) p.quantized
  reference : LayerNormPair.Ranges rw ri rs rb (fun i => value (word ri i)) p.reference
  scaleEqual : ∀ i < 768, word qw (qs + i) = word rw (rs + i)
  biasEqual : ∀ i < 768, word qw (qb + i) = word rw (rb + i)

noncomputable def error (qw qi rw ri : ByteArray) (qs rs : Nat) (inputError : ℝ) (p : Parameters) : ℝ :=
  FiniteErrorBound.upper (LayerNormPair.error qw qi rw ri qs rs (fun _ => inputError) p.quantized p.reference) 768

theorem close (qw qi rw ri : ByteArray) (qs qb rs rb : Nat) (inputError : ℝ) (p : Parameters)
    (h : Ranges qw qi rw ri qs qb rs rb p) (he : Close qi ri 768 inputError) :
    Close (layerNorm qw qi qs qb 1) (layerNorm rw ri rs rb 1) 768 (error qw qi rw ri qs rs inputError p) := by
  intro i hi
  exact (LayerNormPair.component_error qw qi rw ri qs qb rs rb (fun _ => inputError) p.quantized p.reference
    h.quantized h.reference he h.scaleEqual h.biasEqual i hi).2.2.trans (FiniteErrorBound.component_le _ _ i hi)
end Norm

namespace Projection
structure Parameters where
  bounds : Nat → ProjectionPair.Bounds
  activationError : Nat → Nat → ℝ
  weightError : Nat → Nat → ℝ

def Ranges (qw qi rw ri : ByteArray) (l : ProjectionPair.Layout) (p : Parameters) : Prop :=
  ∀ j < l.outputWidth, ProjectionPair.Ranges qw qi rw ri l j (p.activationError j) (p.weightError j) (p.bounds j)

noncomputable def error (qw qi rw ri : ByteArray) (l : ProjectionPair.Layout) (inputError : ℝ) (p : Parameters) : ℝ :=
  FiniteErrorBound.upper (fun j => ProjectionPair.error qw qi rw ri l j (fun _ => inputError)
    (p.activationError j) (p.weightError j) (p.bounds j)) l.outputWidth

theorem close (qw qi rw ri : ByteArray) (l : ProjectionPair.Layout) (inputError : ℝ) (p : Parameters)
    (h : Ranges qw qi rw ri l p) (hw : 64 ∣ l.width) (he : Close qi ri l.width inputError) :
    Close (Quantized.linearGroupedRows qw qi l.qWeight l.qScale l.qBias l.width l.outputWidth 1 true)
      (linearRows rw ri l.rWeight l.rBias l.width l.outputWidth 1) l.outputWidth (error qw qi rw ri l inputError p) := by
  intro j hj
  exact (ProjectionPair.component_error qw qi rw ri l j hj hw (fun _ => inputError)
    (p.activationError j) (p.weightError j) (p.bounds j) (h j hj) he).2.2.trans
      (FiniteErrorBound.component_le (fun j => ProjectionPair.error qw qi rw ri l j (fun _ => inputError)
        (p.activationError j) (p.weightError j) (p.bounds j)) _ j hj)
end Projection

namespace Attention
abbrev Parameters := Nat → AttentionPair.Bounds

def Ranges (qc qq rc rq : ByteArray) (layer position : Nat) (p : Parameters) : Prop :=
  ∀ i < 768, AttentionPair.Ranges qc qq rc rq layer position i (p i)

noncomputable def scoreBound (qc qq rc rq : ByteArray) (layer position i : Nat)
    (cacheError qkvError : ℝ) (p : Parameters) : ℝ :=
  FiniteErrorBound.upper (fun j => AttentionPair.scoreError qc qq rc rq layer position (i / 64) j cacheError qkvError (p i)) (position + 1)

noncomputable def error (qc qq rc rq : ByteArray) (layer position : Nat)
    (cacheError qkvError : ℝ) (p : Parameters) : ℝ :=
  FiniteErrorBound.upper (fun i => AttentionPair.error qc qq rc rq layer position i cacheError qkvError
    (scoreBound qc qq rc rq layer position i cacheError qkvError p) (p i)) 768

theorem close (qc qq rc rq : ByteArray) (layer position : Nat) (hl : layer < 12)
    (cacheError qkvError : ℝ) (p : Parameters) (h : Ranges qc qq rc rq layer position p)
    (hc : Close qc rc (position * 18432) cacheError) (hq : Close qq rq 2304 qkvError) :
    Close (cachedAttention qc qq layer position) (cachedAttention rc rq layer position) 768
      (error qc qq rc rq layer position cacheError qkvError p) := by
  intro i hi
  exact (AttentionPair.component_error qc qq rc rq layer position i hl hi cacheError qkvError
    (scoreBound qc qq rc rq layer position i cacheError qkvError p) (p i) (h i hi) hc hq
    (FiniteErrorBound.nonnegative _ _) (fun j hj => FiniteErrorBound.component_le
      (fun j => AttentionPair.scoreError qc qq rc rq layer position (i / 64) j cacheError qkvError (p i)) _ j hj)).2.2.trans
      (FiniteErrorBound.component_le (fun i => AttentionPair.error qc qq rc rq layer position i cacheError qkvError
        (scoreBound qc qq rc rq layer position i cacheError qkvError p) (p i)) _ i hi)
end Attention

namespace Add
structure Parameters where
  quantized : Nat → Nat
  reference : Nat → Nat

def Ranges (ql qr rl rr : ByteArray) (n : Nat) (p : Parameters) : Prop :=
  ∀ i < n, PointwisePair.AddRanges ql qr rl rr i (p.quantized i) (p.reference i)

noncomputable def error (n : Nat) (leftError rightError : ℝ) (p : Parameters) : ℝ :=
  FiniteErrorBound.upper (fun i => F32AdditionBounds.epsilon (p.quantized i) + (leftError + rightError) +
    F32AdditionBounds.epsilon (p.reference i)) n

theorem close (ql qr rl rr : ByteArray) (n : Nat) (leftError rightError : ℝ) (p : Parameters)
    (h : Ranges ql qr rl rr n p) (hq : n ≤ ql.size / 4) (hr : n ≤ rl.size / 4)
    (hl : Close ql rl n leftError) (hRight : Close qr rr n rightError) :
    Close (addRows ql qr) (addRows rl rr) n (error n leftError rightError p) := by
  intro i hi
  exact (PointwisePair.add_error ql qr rl rr i (p.quantized i) (p.reference i) (by omega) (by omega)
    leftError rightError (h i hi) (hl i hi) (hRight i hi)).trans (FiniteErrorBound.component_le
      (fun i => F32AdditionBounds.epsilon (p.quantized i) + (leftError + rightError) + F32AdditionBounds.epsilon (p.reference i)) _ i hi)
end Add

namespace Activate
structure Parameters where
  quantized : Nat → Gpt2CachedStep.GeluForwardError.Bounds
  reference : Nat → Gpt2CachedStep.GeluForwardError.Bounds

def Ranges (qi ri : ByteArray) (n : Nat) (p : Parameters) : Prop :=
  ∀ i < n, PointwisePair.GeluRanges qi ri i (p.quantized i) (p.reference i)

noncomputable def error (qi ri : ByteArray) (n : Nat) (inputError : ℝ) (p : Parameters) : ℝ :=
  FiniteErrorBound.upper (fun i => Gpt2CachedStep.GeluForwardError.error (word qi i) (p.quantized i) +
    4 * inputError + Gpt2CachedStep.GeluForwardError.error (word ri i) (p.reference i)) n

theorem close (qi ri : ByteArray) (n : Nat) (inputError : ℝ) (p : Parameters)
    (h : Ranges qi ri n p) (hq : n ≤ qi.size / 4) (hr : n ≤ ri.size / 4) (he : Close qi ri n inputError) :
    Close (activate qi) (activate ri) n (error qi ri n inputError p) := by
  intro i hi
  exact (PointwisePair.gelu_error qi ri i (by omega) (by omega) inputError (p.quantized i)
    (p.reference i) (h i hi) (he i hi)).trans (FiniteErrorBound.component_le
      (fun i => Gpt2CachedStep.GeluForwardError.error (word qi i) (p.quantized i) + 4 * inputError +
        Gpt2CachedStep.GeluForwardError.error (word ri i) (p.reference i)) _ i hi)
end Activate

#print axioms Norm.close
#print axioms Projection.close
#print axioms Attention.close
#print axioms Add.close
#print axioms Activate.close
end Project.Gpt2QuantizedCached.Numerical
