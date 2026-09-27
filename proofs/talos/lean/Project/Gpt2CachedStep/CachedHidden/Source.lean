import Project.Gpt2CachedStep.CachedBlock.Spec

namespace Project.Gpt2CachedStep.CachedHidden
open LeanExe.Models.Gpt2 Project.ProofKit

def embedding (weights : ByteArray) (token : UInt32) (position : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE 768 fun channel =>
    LeanExe.Float32.addBits (word weights (token.toNat * 768 + channel))
      (word weights (positionOffset + position * 768 + channel))

def layerStep (weights cache : ByteArray) (position : Nat) (state : ByteArray × ByteArray)
    (layer : Nat) : ByteArray × ByteArray :=
  let result := cachedBlock weights state.1 cache layer position
  (result.hidden, state.2 ++ result.cache)

def layerPrefix (weights cache : ByteArray) (token : UInt32) (position count : Nat) : ByteArray × ByteArray :=
  (List.range count).foldl (layerStep weights cache position) (embedding weights token position, ByteArray.empty)

@[simp] theorem embedding_size (weights : ByteArray) (token : UInt32) (position : Nat) :
    (embedding weights token position).size = 3072 := PackedSource.generate_size ..

@[simp] theorem layerPrefix_zero (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    layerPrefix weights cache token position 0 = (embedding weights token position, ByteArray.empty) := rfl

theorem layerPrefix_succ (weights cache : ByteArray) (token : UInt32) (position count : Nat) :
    layerPrefix weights cache token position (count + 1) =
      layerStep weights cache position (layerPrefix weights cache token position count) count := by
  simp only [layerPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem layerPrefix_sizes (weights cache : ByteArray) (token : UInt32) (position count : Nat) :
    (layerPrefix weights cache token position count).1.size = 3072 ∧
      (layerPrefix weights cache token position count).2.size = count * 6144 := by
  induction count with
  | zero => exact ⟨embedding_size .., rfl⟩
  | succ count ih =>
    rw [layerPrefix_succ]
    constructor
    · exact CachedBlock.Spec.cachedBlock_hidden_size _ _ _ _ _ ih.1
    · simp only [layerStep, ByteArray.size_append, ih.2, CachedBlock.Spec.cachedBlock_cache_size]
      omega

theorem cachedHidden_eq (weights cache : ByteArray) (token : UInt32) (position : Nat) :
    cachedHidden weights cache token position =
      { hidden := (layerPrefix weights cache token position 12).1,
        cache := cache ++ (layerPrefix weights cache token position 12).2 } := by
  simp only [cachedHidden, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel_right, Nat.div_one]
  rfl

#print axioms cachedHidden_eq
#print axioms layerPrefix_sizes

end Project.Gpt2CachedStep.CachedHidden
