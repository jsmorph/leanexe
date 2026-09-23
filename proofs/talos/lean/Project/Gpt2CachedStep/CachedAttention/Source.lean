import Project.Gpt2CachedStep.CachedAttention.Compute
import Project.ProofKit.F32Add
import Project.ProofKit.F32Mul
import Project.ProofKit.PackedSource

namespace Project.Gpt2CachedStep.CachedAttention
open LeanExe.Models.Gpt2

@[simp] theorem mixedPrefix_zero (cache qkv probabilities : ByteArray) (layer position index : Nat) :
    mixedPrefix cache qkv probabilities layer position index 0 = 0 := rfl

theorem mixedPrefix_succ (cache qkv probabilities : ByteArray) (layer position index count : Nat) :
    mixedPrefix cache qkv probabilities layer position index (count + 1) =
      Wasm.IEEE32.add (mixedPrefix cache qkv probabilities layer position index count)
        (Wasm.IEEE32.mul (word probabilities (index / 64 * (position + 1) + count))
          (cachedKv cache qkv layer position count (768 + index))) := by
  simp only [mixedPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Project.ProofKit.F32Add.add_eq, Project.ProofKit.F32Mul.mul_eq]

theorem cachedAttention_eq (cache qkv : ByteArray) (layer position : Nat) :
    cachedAttention cache qkv layer position =
      let scoreValues := scores cache qkv layer position
      let maximumValues := maxima scoreValues (position + 1)
      let exponentialValues := exponentials scoreValues maximumValues (position + 1)
      let sumValues := sums exponentialValues (position + 1)
      let probabilityValues := probabilities exponentialValues sumValues (position + 1)
      mixed cache qkv probabilityValues layer position := by
  unfold cachedAttention mixed
  dsimp only
  congr 1
  funext index
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel_right, Nat.div_one]
  rfl

@[simp] theorem scores_size (cache qkv : ByteArray) (layer position : Nat) :
    (scores cache qkv layer position).size = 4 * (12 * (position + 1)) :=
  Project.ProofKit.PackedSource.generate_size ..

@[simp] theorem maxima_size (scoreValues : ByteArray) (size : Nat) :
    (maxima scoreValues size).size = 48 := Project.ProofKit.PackedSource.generate_size ..

@[simp] theorem exponentials_size (scoreValues maximumValues : ByteArray) (size : Nat) :
    (exponentials scoreValues maximumValues size).size = 4 * (12 * size) :=
  Project.ProofKit.PackedSource.generate_size ..

@[simp] theorem sums_size (exponentialValues : ByteArray) (size : Nat) :
    (sums exponentialValues size).size = 48 := Project.ProofKit.PackedSource.generate_size ..

@[simp] theorem probabilities_size (exponentialValues sumValues : ByteArray) (size : Nat) :
    (probabilities exponentialValues sumValues size).size = 4 * (12 * size) :=
  Project.ProofKit.PackedSource.generate_size ..

@[simp] theorem mixed_size (cache qkv probabilityValues : ByteArray) (layer position : Nat) :
    (mixed cache qkv probabilityValues layer position).size = 3072 :=
  Project.ProofKit.PackedSource.generate_size ..

#print axioms cachedAttention_eq

end Project.Gpt2CachedStep.CachedAttention
