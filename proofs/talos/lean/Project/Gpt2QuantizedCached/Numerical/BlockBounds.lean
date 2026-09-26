import Project.Gpt2QuantizedCached.Numerical.BlockSource

namespace Project.Gpt2QuantizedCached.Numerical.Block
open LeanExe.Models.Gpt2 Project.ProofKit

structure Parameters where
  normalized : Norm.Parameters
  qkv : Projection.Parameters
  mixed : Attention.Parameters
  projected : Projection.Parameters
  residual : Add.Parameters
  normalized2 : Norm.Parameters
  expanded : Projection.Parameters
  activated : Activate.Parameters
  projected2 : Projection.Parameters
  hidden : Add.Parameters

structure Errors where
  normalized : ℝ
  qkv : ℝ
  mixed : ℝ
  projected : ℝ
  residual : ℝ
  normalized2 : ℝ
  expanded : ℝ
  activated : ℝ
  projected2 : ℝ
  hidden : ℝ

noncomputable def errors (qw qi qc rw ri rc : ByteArray) (layer position : Nat) (qt rt : Tensors)
    (inputError cacheError : ℝ) (p : Parameters) : Errors :=
  let normalized := Norm.error qw qi rw ri (qBase layer / 4) (rBase layer) inputError p.normalized
  let qkv := Projection.error qw qt.normalized rw rt.normalized (qkvLayout layer) normalized p.qkv
  let mixed := Attention.error qc qt.qkv rc rt.qkv layer position cacheError qkv p.mixed
  let projected := Projection.error qw qt.mixed rw rt.mixed (attentionLayout layer) mixed p.projected
  let residual := Add.error 768 inputError projected p.residual
  let normalized2 := Norm.error qw qt.residual rw rt.residual ((qBase layer + Quantized.ln2ScaleOffset) / 4)
    (rBase layer + ln2ScaleOffset) residual p.normalized2
  let expanded := Projection.error qw qt.normalized2 rw rt.normalized2 (expansionLayout layer) normalized2 p.expanded
  let activated := Activate.error qt.expanded rt.expanded 3072 expanded p.activated
  let projected2 := Projection.error qw qt.activated rw rt.activated (contractionLayout layer) activated p.projected2
  ⟨normalized, qkv, mixed, projected, residual, normalized2, expanded, activated, projected2,
    Add.error 768 residual projected2 p.hidden⟩

structure Ranges (qw qi qc rw ri rc : ByteArray) (layer position : Nat) (qt rt : Tensors) (p : Parameters) : Prop where
  normalized : Norm.Ranges qw qi rw ri (qBase layer / 4) (qBase layer / 4 + 768)
    (rBase layer) (rBase layer + 768) p.normalized
  qkv : Projection.Ranges qw qt.normalized rw rt.normalized (qkvLayout layer) p.qkv
  mixed : Attention.Ranges qc qt.qkv rc rt.qkv layer position p.mixed
  projected : Projection.Ranges qw qt.mixed rw rt.mixed (attentionLayout layer) p.projected
  residual : Add.Ranges qi qt.projected ri rt.projected 768 p.residual
  normalized2 : Norm.Ranges qw qt.residual rw rt.residual ((qBase layer + Quantized.ln2ScaleOffset) / 4)
    ((qBase layer + Quantized.ln2BiasOffset) / 4) (rBase layer + ln2ScaleOffset) (rBase layer + ln2BiasOffset) p.normalized2
  expanded : Projection.Ranges qw qt.normalized2 rw rt.normalized2 (expansionLayout layer) p.expanded
  activated : Activate.Ranges qt.expanded rt.expanded 3072 p.activated
  projected2 : Projection.Ranges qw qt.activated rw rt.activated (contractionLayout layer) p.projected2
  hidden : Add.Ranges qt.residual qt.projected2 rt.residual rt.projected2 768 p.hidden

structure TensorErrors (qt rt : Tensors) (e : Errors) : Prop where
  normalized : Close qt.normalized rt.normalized 768 e.normalized
  qkv : Close qt.qkv rt.qkv 2304 e.qkv
  mixed : Close qt.mixed rt.mixed 768 e.mixed
  projected : Close qt.projected rt.projected 768 e.projected
  residual : Close qt.residual rt.residual 768 e.residual
  normalized2 : Close qt.normalized2 rt.normalized2 768 e.normalized2
  expanded : Close qt.expanded rt.expanded 3072 e.expanded
  activated : Close qt.activated rt.activated 3072 e.activated
  projected2 : Close qt.projected2 rt.projected2 768 e.projected2
  hidden : Close qt.hidden rt.hidden 768 e.hidden

end Project.Gpt2QuantizedCached.Numerical.Block
