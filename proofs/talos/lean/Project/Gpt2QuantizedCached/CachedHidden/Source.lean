import Project.Gpt2QuantizedCached.CachedBlock.Spec
import Project.Gpt2QuantizedCached.CachedBlock.Sizes
import Project.Gpt2QuantizedCached.Embedding.Spec

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.CachedHidden
open LeanExe.Models.Gpt2.Quantized Project.ProofKit

abbrev LayerState := ByteArray × ByteArray × UInt64

def layerStep (weights cache : ByteArray) (position : Nat) (state : LayerState) (layer : Nat) : LayerState :=
  if state.2.2 == 0 then
    let result := cachedBlock weights state.1 cache layer position
    (result.hidden, state.2.1 ++ result.cache, result.status)
  else state

def layerPrefix (weights cache : ByteArray) (token : UInt32) (position count : Nat) : LayerState :=
  (List.range count).foldl (layerStep weights cache position) (embedding weights token position, .empty, 0)

theorem layerPrefix_fold (weights cache : ByteArray) (token : UInt32) (position count : Nat) :
    layerPrefix weights cache token position count =
      (List.range count).foldl (layerStep weights cache position) (embedding weights token position, .empty, 0) := rfl

theorem layerPrefix_zero (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    layerPrefix weights cache token position 0 = (embedding weights token position, .empty, 0) := rfl

theorem layerPrefix_succ (weights cache : ByteArray) (token : UInt32) (position count : Nat) :
    layerPrefix weights cache token position (count + 1) =
      layerStep weights cache position (layerPrefix weights cache token position count) count := by
  simp only [layerPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem yield_ite {α : Type} (condition : Bool) (left right : α) :
    (if condition then pure (.yield left) else pure (.yield right) : Id (ForInStep α)) =
      pure (.yield (if condition then left else right)) := by
  cases condition <;> rfl

theorem layerLoop_foldl (weights cache : ByteArray) (position : Nat)
    (layers : List Nat) (initial : LayerState) :
    (forIn layers initial (fun layer state =>
      if state.2.2 == 0 then
        pure (.yield ((cachedBlock weights state.1 cache layer position).hidden,
          state.2.1 ++ (cachedBlock weights state.1 cache layer position).cache,
          (cachedBlock weights state.1 cache layer position).status))
      else pure (.yield (state.1, state.2.1, state.2.2))) : Id LayerState) =
      layers.foldl (layerStep weights cache position) initial := by
  simp only [yield_ite, List.forIn_pure_yield_eq_foldl]
  rfl

theorem finishLayerLoop (state : Id LayerState) (cache : ByteArray) :
    (Id.run do
      let result ← state
      if result.2.2 != 0 then
        pure ({ status := result.2.2, hidden := .empty, cache := .empty } : HiddenResult)
      else pure { status := 0, hidden := result.1, cache := cache ++ result.2.1 }) =
      if state.2.2 != 0 then { status := state.2.2, hidden := .empty, cache := .empty }
      else { status := 0, hidden := state.1, cache := cache ++ state.2.1 } := by
  rfl

theorem cachedHidden_eq (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    cachedHidden weights cache token position =
      let result := layerPrefix weights cache token position 12
      if result.2.2 != 0 then { status := result.2.2, hidden := .empty, cache := .empty }
      else { status := 0, hidden := result.1, cache := cache ++ result.2.1 } := by
  simp only [cachedHidden, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range', Nat.sub_zero, Nat.add_sub_cancel_right, Nat.div_one,
    layerLoop_foldl, ← layerPrefix_fold]
  exact finishLayerLoop _ _

#print axioms cachedHidden_eq
end Project.Gpt2QuantizedCached.CachedHidden
