import Project.Gpt2QuantizedCached.Numerical.BlockBounds

namespace Project.Gpt2QuantizedCached.Numerical.Block
open LeanExe.Models.Gpt2 Project.ProofKit

set_option maxRecDepth 8192

theorem tensors_error (qw qi qc rw ri rc : ByteArray) (layer position : Nat) (hl : layer < 12)
    (hqi : qi.size = 3072) (hri : ri.size = 3072) (inputError cacheError : ℝ) (p : Parameters)
    (h : Ranges qw qi qc rw ri rc layer position (quantizedTensors qw qi qc layer position)
      (referenceTensors rw ri rc layer position) p)
    (he : Close qi ri 768 inputError) (hc : Close qc rc (position * 18432) cacheError) :
    TensorErrors (quantizedTensors qw qi qc layer position) (referenceTensors rw ri rc layer position)
      (errors qw qi qc rw ri rc layer position (quantizedTensors qw qi qc layer position)
        (referenceTensors rw ri rc layer position) inputError cacheError p) := by
  let qt := quantizedTensors qw qi qc layer position
  let rt := referenceTensors rw ri rc layer position
  let e := errors qw qi qc rw ri rc layer position qt rt inputError cacheError p
  have qs : qt.Sizes := Gpt2QuantizedCached.CachedBlock.tensors_sizes qw qi qc layer position hqi
  have rs : rt.Sizes := reference_sizes rw ri rc layer position hri
  have hn : Close qt.normalized rt.normalized 768 e.normalized :=
    Norm.close qw qi rw ri (qBase layer / 4) (qBase layer / 4 + 768)
      (rBase layer) (rBase layer + 768) inputError p.normalized h.normalized he
  have hq : Close qt.qkv rt.qkv 2304 e.qkv :=
    Projection.close qw qt.normalized rw rt.normalized (qkvLayout layer) e.normalized p.qkv h.qkv (by change 64 ∣ 768; decide) hn
  have hm : Close qt.mixed rt.mixed 768 e.mixed :=
    Attention.close qc qt.qkv rc rt.qkv layer position hl cacheError e.qkv p.mixed h.mixed hc hq
  have hp : Close qt.projected rt.projected 768 e.projected :=
    Projection.close qw qt.mixed rw rt.mixed (attentionLayout layer) e.mixed p.projected h.projected (by change 64 ∣ 768; decide) hm
  have hr : Close qt.residual rt.residual 768 e.residual :=
    Add.close qi qt.projected ri rt.projected 768 inputError e.projected p.residual h.residual
      (by rw [hqi]) (by rw [hri]) he hp
  have hn2 : Close qt.normalized2 rt.normalized2 768 e.normalized2 :=
    Norm.close qw qt.residual rw rt.residual ((qBase layer + Quantized.ln2ScaleOffset) / 4)
      ((qBase layer + Quantized.ln2BiasOffset) / 4) (rBase layer + ln2ScaleOffset) (rBase layer + ln2BiasOffset)
      e.residual p.normalized2 h.normalized2 hr
  have hf : Close qt.expanded rt.expanded 3072 e.expanded :=
    Projection.close qw qt.normalized2 rw rt.normalized2 (expansionLayout layer) e.normalized2
      p.expanded h.expanded (by change 64 ∣ 768; decide) hn2
  have ha : Close qt.activated rt.activated 3072 e.activated :=
    Activate.close qt.expanded rt.expanded 3072 e.expanded p.activated h.activated
      (by rw [qs.expanded]) (by rw [rs.expanded]) hf
  have hp2 : Close qt.projected2 rt.projected2 768 e.projected2 :=
    Projection.close qw qt.activated rw rt.activated (contractionLayout layer) e.activated
      p.projected2 h.projected2 (by change 64 ∣ 3072; decide) ha
  have hout : Close qt.hidden rt.hidden 768 e.hidden :=
    Add.close qt.residual qt.projected2 rt.residual rt.projected2 768 e.residual e.projected2
      p.hidden h.hidden (by rw [qs.residual]) (by rw [rs.residual]) hr hp2
  exact ⟨hn, hq, hm, hp, hr, hn2, hf, ha, hp2, hout⟩

theorem block_error (qw qi qc rw ri rc : ByteArray) (layer position : Nat) (hl : layer < 12)
    (hqi : qi.size = 3072) (hri : ri.size = 3072) (inputError cacheError : ℝ) (p : Parameters)
    (h : Ranges qw qi qc rw ri rc layer position (quantizedTensors qw qi qc layer position)
      (referenceTensors rw ri rc layer position) p)
    (accepted : (quantizedTensors qw qi qc layer position).accepted = true)
    (he : Close qi ri 768 inputError) (hc : Close qc rc (position * 18432) cacheError) :
    let e := errors qw qi qc rw ri rc layer position (quantizedTensors qw qi qc layer position)
      (referenceTensors rw ri rc layer position) inputError cacheError p
    Close (Quantized.cachedBlock qw qi qc layer position).hidden (cachedBlock rw ri rc layer position).hidden 768 e.hidden ∧
      Close (Quantized.cachedBlock qw qi qc layer position).cache (cachedBlock rw ri rc layer position).cache 1536 e.qkv := by
  have hT := tensors_error qw qi qc rw ri rc layer position hl hqi hri inputError cacheError p h he hc
  dsimp only
  rw [quantized_hidden qw qi qc layer position accepted, reference_hidden,
    quantized_cache qw qi qc layer position accepted, reference_cache]
  exact ⟨hT.hidden, CacheError.update_error _ _ _ hT.qkv⟩

#print axioms tensors_error
#print axioms block_error
end Project.Gpt2QuantizedCached.Numerical.Block
