import LeanExe.Models.Gpt2.Kernel
import Project.ProofKit.F32Add
import Project.ProofKit.F32Mul

namespace Project.Gpt2AttentionScore

open LeanExe.Models.Gpt2

def dotPrefix (input : ByteArray) (target source head count : Nat) : UInt32 :=
  (List.range count).foldl (fun total index =>
    LeanExe.Float32.addBits total (LeanExe.Float32.mulBits
      (word input (target * 2304 + head * 64 + index))
      (word input (source * 2304 + 768 + head * 64 + index)))) 0

@[simp] theorem dotPrefix_zero (input : ByteArray) (target source head : Nat) :
    dotPrefix input target source head 0 = 0 := rfl

theorem dotPrefix_succ (input : ByteArray) (target source head count : Nat) :
    dotPrefix input target source head (count + 1) =
      Wasm.IEEE32.add (dotPrefix input target source head count) (Wasm.IEEE32.mul
        (word input (target * 2304 + head * 64 + count))
        (word input (source * 2304 + 768 + head * 64 + count))) := by
  simp only [dotPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Project.ProofKit.F32Add.add_eq, Project.ProofKit.F32Mul.mul_eq]

theorem attentionScore_eq (input : ByteArray) (target source head : Nat) :
    attentionScore input target source head =
      Wasm.IEEE32.mul (dotPrefix input target source head 64) 0x3E000000 := by
  simp only [attentionScore, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range']
  change LeanExe.Float32.mulBits (dotPrefix input target source head 64) _ = _
  exact Project.ProofKit.F32Mul.mul_eq _ _

end Project.Gpt2AttentionScore
