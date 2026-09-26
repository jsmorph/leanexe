import Project.Gpt2QuantizedCached.Numerical.BlockError
import Project.Gpt2QuantizedCached.Numerical.EmbeddingPair
import Project.Gpt2QuantizedCached.Numerical.AppendError
import Project.Gpt2QuantizedCached.CachedHidden.Sizes

namespace Project.Gpt2QuantizedCached.Numerical.Hidden
open LeanExe.Models.Gpt2 Project.ProofKit

abbrev qState := Gpt2QuantizedCached.CachedHidden.layerPrefix
abbrev rState := Gpt2CachedStep.CachedHidden.layerPrefix

structure Parameters where
  embedding : EmbeddingPair.Parameters
  block : Nat → Block.Parameters

noncomputable def nextErrors (qw qc rw rc : ByteArray) (qi ri : ByteArray) (layer position : Nat)
    (hiddenError updateError cacheError : ℝ) (p : Block.Parameters) : ℝ × ℝ :=
  let qt := Block.quantizedTensors qw qi qc layer position
  let rt := Block.referenceTensors rw ri rc layer position
  let e := Block.errors qw qi qc rw ri rc layer position qt rt hiddenError cacheError p
  (e.hidden, max updateError e.qkv)

noncomputable def layerErrors (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat)
    (cacheError : ℝ) (p : Parameters) : Nat → ℝ × ℝ
  | 0 => (EmbeddingPair.error p.embedding, 0)
  | count + 1 =>
    let previous := layerErrors qw qc rw rc token position cacheError p count
    nextErrors qw qc rw rc (qState qw qc token position count).1 (rState rw rc token position count).1
      count position previous.1 previous.2 cacheError (p.block count)

structure Ranges (qw qc rw rc : ByteArray) (token : UInt32) (position : Nat) (p : Parameters) : Prop where
  embedding : EmbeddingPair.Ranges qw rw token position p.embedding
  blocks : ∀ layer < 12,
    let qi := (qState qw qc token position layer).1
    let ri := (rState rw rc token position layer).1
    Block.Ranges qw qi qc rw ri rc layer position (Block.quantizedTensors qw qi qc layer position)
      (Block.referenceTensors rw ri rc layer position) (p.block layer)
  accepted : ∀ layer < 12,
    (Block.quantizedTensors qw (qState qw qc token position layer).1 qc layer position).accepted = true

structure StateBound (q : Gpt2QuantizedCached.CachedHidden.LayerState) (r : ByteArray × ByteArray)
    (count : Nat) (hiddenError updateError : ℝ) : Prop where
  status : q.2.2 = 0
  hiddenSize : q.1.size = 3072
  updateSize : q.2.1.size = count * 6144
  referenceHiddenSize : r.1.size = 3072
  referenceUpdateSize : r.2.size = count * 6144
  hiddenError : Close q.1 r.1 768 hiddenError
  updateError : Close q.2.1 r.2 (count * 1536) updateError

abbrev PrefixBound (qw qc rw rc : ByteArray) (token : UInt32) (position count : Nat)
    (cacheError : ℝ) (p : Parameters) : Prop :=
  StateBound (qState qw qc token position count) (rState rw rc token position count) count
    (layerErrors qw qc rw rc token position cacheError p count).1
    (layerErrors qw qc rw rc token position cacheError p count).2

end Project.Gpt2QuantizedCached.Numerical.Hidden
