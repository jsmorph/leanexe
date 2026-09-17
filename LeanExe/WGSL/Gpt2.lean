import LeanExe.WGSL.Compile

/-! Lean definitions compiled for the six GPT-2 dense products. Each output is
one source-ordered binary32 dot product. The compiler reads these bodies and
recursively translates the fold callback; no WGSL template is selected here. -/
namespace LeanExe.WGSL.Gpt2
open Source

/-- A packed single-row dense product, with an explicit arithmetic interpretation. -/
def dense (inner cols : Nat) : Kernel := fun ar a b _ col =>
  Source.fold inner 0 fun k acc => ar.add acc (ar.mul (a k) (b (k * cols + col)))

@[wgsl] def qkv : Kernel := fun ar a b row col => dense 768 2304 ar a b row col
@[wgsl] def attention : Kernel := fun ar a b row col => dense 768 768 ar a b row col
@[wgsl] def expansion : Kernel := fun ar a b row col => dense 768 3072 ar a b row col
@[wgsl] def projection : Kernel := fun ar a b row col => dense 3072 768 ar a b row col
@[wgsl] def vocabularyLeft : Kernel := fun ar a b row col => dense 768 25129 ar a b row col
@[wgsl] def vocabularyRight : Kernel := fun ar a b row col => dense 768 25128 ar a b row col

end LeanExe.WGSL.Gpt2
