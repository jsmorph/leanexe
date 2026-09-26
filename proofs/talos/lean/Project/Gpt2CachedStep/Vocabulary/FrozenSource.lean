import LeanExe.Models.Gpt2.Inference
import Project.ProofKit.F32Add
import Project.ProofKit.F32Mul

namespace Project.Gpt2CachedStep.Frozen.Vocabulary
open LeanExe.Models.Gpt2

def dotPrefix (weights input : ByteArray) (token count : Nat) : UInt32 :=
  (List.range count).foldl (fun total channel => LeanExe.Float32.addBits total
    (LeanExe.Float32.mulBits (word input channel) (word weights (token * 768 + channel)))) 0

@[simp] theorem dotPrefix_zero (weights input : ByteArray) (token : Nat) :
    dotPrefix weights input token 0 = 0 := rfl

theorem dotPrefix_succ (weights input : ByteArray) (token count : Nat) :
    dotPrefix weights input token (count + 1) = Wasm.IEEE32.add (dotPrefix weights input token count)
      (Wasm.IEEE32.mul (word input count) (word weights (token * 768 + count))) := by
  simp only [dotPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
    Project.ProofKit.F32Add.add_eq, Project.ProofKit.F32Mul.mul_eq]

theorem vocabularyHead_eq (weights input : ByteArray) : vocabularyHead weights input =
    LeanExe.Packed.generateUInt32LE 50257 (fun token => dotPrefix weights input token 768) := by
  simp only [vocabularyHead, vocabulary, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range']
  rfl

#print axioms vocabularyHead_eq

end Project.Gpt2CachedStep.Frozen.Vocabulary
