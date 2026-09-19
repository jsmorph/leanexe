import LeanExe.WGSL.Gpt2

/-! Kernels for the parent's packed FP32 model. B contains the matrix in
input-major order followed by its bias vector. The bias addition is the last
FP32 operation, as in `LeanExe.Models.Gpt2.linearRows`. -/
namespace LeanExe.WGSL.Gpt2Packed
open Source

def biased (inner cols : Nat) : Kernel := fun ar a b row col =>
  let dot := Gpt2.dense inner cols ar a b row col
  ar.add dot (b (inner * cols + col))

@[wgsl] def qkv : Kernel := fun ar a b row col => biased 768 2304 ar a b row col
@[wgsl] def attention : Kernel := fun ar a b row col => biased 768 768 ar a b row col
@[wgsl] def expansion : Kernel := fun ar a b row col => biased 768 3072 ar a b row col
@[wgsl] def projection : Kernel := fun ar a b row col => biased 3072 768 ar a b row col

end LeanExe.WGSL.Gpt2Packed
