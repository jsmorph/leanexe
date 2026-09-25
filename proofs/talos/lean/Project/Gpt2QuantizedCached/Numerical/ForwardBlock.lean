import Project.Gpt2QuantizedCached.Numerical.ForwardUpper
import Project.Gpt2QuantizedCached.Numerical.NormalizationPairUpper
import Project.Gpt2QuantizedCached.Numerical.ProjectionUpper
import Project.Gpt2QuantizedCached.Numerical.PointwiseUpper
import Project.Gpt2QuantizedCached.Numerical.AttentionUpper
import Project.Gpt2QuantizedCached.Numerical.BlockSource

namespace Project.Gpt2QuantizedCached.Numerical.ForwardUpper
open LeanExe.Models.Gpt2 Project.ProofKit

def ProjectionConditions (qw qi rw ri : ByteArray) (l : ProjectionPair.Layout)
    (d : OperationUpper.ProjectionData) : Prop := ∃ ex ew, ProjectionUpper.Conditions qw qi rw ri l d ex ew

theorem projection_close (qw qi rw ri : ByteArray) (l : ProjectionPair.Layout) (d : OperationUpper.ProjectionData)
    (h : ProjectionConditions qw qi rw ri l d) (hw : 64 ∣ l.width)
    (E : Nat) (he : Close qi ri l.width (DyadicUpper.value E)) :
    Close (Quantized.linearGroupedRows qw qi l.qWeight l.qScale l.qBias l.width l.outputWidth 1 true)
      (linearRows rw ri l.rWeight l.rBias l.width l.outputWidth 1) l.outputWidth
      (DyadicUpper.value (OperationUpper.project l.width true d E)) := by
  obtain ⟨ex, ew, h⟩ := h
  exact ProjectionUpper.learned_close qw qi rw ri l d ex ew h hw E he

def NormConditions (qw qi rw ri : ByteArray) (qs qb rs rb : Nat) (d : NormalizationUpper.PairData) : Prop :=
  Norm.Ranges qw qi rw ri qs qb rs rb (NormalizationUpper.pairParameters d) ∧
    NormalizationUpper.Magnitudes qw qi rw ri qs rs d

structure BlockConditions (qw qi qc rw ri rc : ByteArray) (layer position : Nat)
    (qt rt : Block.Tensors) (d : BlockData) : Prop where
  normalized : NormConditions qw qi rw ri (Block.qBase layer / 4) (Block.qBase layer / 4 + 768)
    (Block.rBase layer) (Block.rBase layer + 768) d.normalized
  qkv : ProjectionConditions qw qt.normalized rw rt.normalized (Block.qkvLayout layer) d.qkv
  attention : Attention.Ranges qc qt.qkv rc rt.qkv layer position
    (fun _ => AttentionUpper.parameters d.quantizedAttention d.referenceAttention)
  attentionMagnitudes : AttentionUpper.Magnitudes qt.qkv rc rt.qkv layer position d.queryMagnitude d.keyMagnitude d.referenceAttention
  projected : ProjectionConditions qw qt.mixed rw rt.mixed (Block.attentionLayout layer) d.projected
  residual : Add.Ranges qi qt.projected ri rt.projected 768 ⟨fun _ => d.residualQuantized, fun _ => d.residualReference⟩
  normalized2 : NormConditions qw qt.residual rw rt.residual ((Block.qBase layer + Quantized.ln2ScaleOffset) / 4)
    ((Block.qBase layer + Quantized.ln2BiasOffset) / 4) (Block.rBase layer + ln2ScaleOffset) (Block.rBase layer + ln2BiasOffset) d.normalized2
  expanded : ProjectionConditions qw qt.normalized2 rw rt.normalized2 (Block.expansionLayout layer) d.expanded
  activated : ∀ i < 3072, PointwisePair.GeluRanges qt.expanded rt.expanded i
    Gpt2CachedStep.GeluUniform.bounds Gpt2CachedStep.GeluUniform.bounds
  projected2 : ProjectionConditions qw qt.activated rw rt.activated (Block.contractionLayout layer) d.projected2
  hidden : Add.Ranges qt.residual qt.projected2 rt.residual rt.projected2 768 ⟨fun _ => d.hiddenQuantized, fun _ => d.hiddenReference⟩

theorem block_close (qw qi qc rw ri rc : ByteArray) (layer position E C : Nat) (d : BlockData)
    (hl : layer < 12) (hqi : qi.size = 3072) (hri : ri.size = 3072)
    (h : BlockConditions qw qi qc rw ri rc layer position (Block.quantizedTensors qw qi qc layer position)
      (Block.referenceTensors rw ri rc layer position) d)
    (he : Close qi ri 768 (DyadicUpper.value E)) (hc : Close qc rc (position * 18432) (DyadicUpper.value C)) :
    Close (Block.quantizedTensors qw qi qc layer position).hidden (Block.referenceTensors rw ri rc layer position).hidden
      768 (DyadicUpper.value (block d position E C).hidden) ∧
    Close (Block.quantizedTensors qw qi qc layer position).qkv (Block.referenceTensors rw ri rc layer position).qkv
      2304 (DyadicUpper.value (block d position E C).qkv) := by
  let qt := Block.quantizedTensors qw qi qc layer position
  let rt := Block.referenceTensors rw ri rc layer position
  let e := block d position E C
  have qs := Gpt2QuantizedCached.CachedBlock.tensors_sizes qw qi qc layer position hqi
  have rs := Block.reference_sizes rw ri rc layer position hri
  have hn : Close qt.normalized rt.normalized 768 (DyadicUpper.value e.normalized) :=
    NormalizationUpper.pair_close qw qi rw ri _ _ _ _ E d.normalized h.normalized.1 h.normalized.2 he
  have hq : Close qt.qkv rt.qkv 2304 (DyadicUpper.value e.qkv) :=
    projection_close qw qt.normalized rw rt.normalized (Block.qkvLayout layer) d.qkv h.qkv (by change 64 ∣ 768; decide) _ hn
  have hm : Close qt.mixed rt.mixed 768 (DyadicUpper.value e.mixed) :=
    AttentionUpper.close qc qt.qkv rc rt.qkv layer position _ _ _ C hl _ _ h.attention h.attentionMagnitudes hc hq
  have hp : Close qt.projected rt.projected 768 (DyadicUpper.value e.projected) :=
    projection_close qw qt.mixed rw rt.mixed (Block.attentionLayout layer) d.projected h.projected (by change 64 ∣ 768; decide) _ hm
  have hr : Close qt.residual rt.residual 768 (DyadicUpper.value e.residual) :=
    PointwiseUpper.residual_close qi qt.projected ri rt.projected 768 E _ _ _ h.residual
      (by rw [hqi]) (by rw [hri]) he hp
  have hn2 : Close qt.normalized2 rt.normalized2 768 (DyadicUpper.value e.normalized2) :=
    NormalizationUpper.pair_close qw qt.residual rw rt.residual _ _ _ _ _ d.normalized2 h.normalized2.1 h.normalized2.2 hr
  have hf : Close qt.expanded rt.expanded 3072 (DyadicUpper.value e.expanded) :=
    projection_close qw qt.normalized2 rw rt.normalized2 (Block.expansionLayout layer) d.expanded h.expanded (by change 64 ∣ 768; decide) _ hn2
  have ha : Close qt.activated rt.activated 3072 (DyadicUpper.value e.activated) :=
    PointwiseUpper.gelu_close qt.expanded rt.expanded 3072 _ h.activated (by rw [qs.expanded]) (by rw [rs.expanded]) hf
  have hp2 : Close qt.projected2 rt.projected2 768 (DyadicUpper.value e.projected2) :=
    projection_close qw qt.activated rw rt.activated (Block.contractionLayout layer) d.projected2 h.projected2 (by change 64 ∣ 3072; decide) _ ha
  exact ⟨PointwiseUpper.residual_close qt.residual qt.projected2 rt.residual rt.projected2 768 _ _ _ _ h.hidden
    (by rw [qs.residual]) (by rw [rs.residual]) hr hp2, hq⟩

#print axioms block_close
end Project.Gpt2QuantizedCached.Numerical.ForwardUpper
