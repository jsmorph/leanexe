import LeanExe.Models.Gpt2.Cached
import Project.ProofKit.F32Add
import Project.ProofKit.F32Mul

namespace Project.Gpt2CachedStep.CachedScore
open LeanExe.Models.Gpt2

def dotPrefix (cache qkv : ByteArray) (layer position source head count : Nat) : UInt32 :=
  (List.range count).foldl (fun total channel =>
    LeanExe.Float32.addBits total (LeanExe.Float32.mulBits
      (word qkv (head * 64 + channel))
      (cachedKv cache qkv layer position source (head * 64 + channel)))) 0

@[simp] theorem dotPrefix_zero (cache qkv : ByteArray) (layer position source head : Nat) :
    dotPrefix cache qkv layer position source head 0 = 0 := rfl

theorem dotPrefix_succ (cache qkv : ByteArray) (layer position source head count : Nat) :
    dotPrefix cache qkv layer position source head (count + 1) =
      Wasm.IEEE32.add (dotPrefix cache qkv layer position source head count) (Wasm.IEEE32.mul
        (word qkv (head * 64 + count))
        (cachedKv cache qkv layer position source (head * 64 + count))) := by
  simp only [dotPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Project.ProofKit.F32Add.add_eq, Project.ProofKit.F32Mul.mul_eq]

theorem cachedScore_eq (cache qkv : ByteArray) (layer position source head : Nat) :
    cachedScore cache qkv layer position source head =
      Wasm.IEEE32.mul (dotPrefix cache qkv layer position source head 64) 0x3E000000 := by
  simp only [cachedScore, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range']
  change LeanExe.Float32.mulBits (dotPrefix cache qkv layer position source head 64) _ = _
  exact Project.ProofKit.F32Mul.mul_eq _ _

#print axioms cachedScore_eq

end Project.Gpt2CachedStep.CachedScore
