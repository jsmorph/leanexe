import LeanExe.Models.Gpt2.Kernel
import Project.ProofKit.F32Add
import Project.ProofKit.F32Mul

namespace Project.Gpt2LinearRows

open LeanExe.Models.Gpt2

def dotPrefix (weights input : ByteArray) (weightOffset inputWidth outputWidth row column count : Nat) : UInt32 :=
  (List.range count).foldl (fun total index =>
    LeanExe.Float32.addBits total (LeanExe.Float32.mulBits
      (word input (row * inputWidth + index))
      (word weights (weightOffset + index * outputWidth + column)))) 0

@[simp] theorem dotPrefix_zero (weights input : ByteArray)
    (weightOffset inputWidth outputWidth row column : Nat) :
    dotPrefix weights input weightOffset inputWidth outputWidth row column 0 = 0 := rfl

theorem dotPrefix_succ (weights input : ByteArray)
    (weightOffset inputWidth outputWidth row column count : Nat) :
    dotPrefix weights input weightOffset inputWidth outputWidth row column (count + 1) =
      Wasm.IEEE32.add (dotPrefix weights input weightOffset inputWidth outputWidth row column count)
        (Wasm.IEEE32.mul (word input (row * inputWidth + count))
          (word weights (weightOffset + count * outputWidth + column))) := by
  simp only [dotPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Project.ProofKit.F32Add.add_eq, Project.ProofKit.F32Mul.mul_eq]

def value (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth row column : Nat) : UInt32 :=
  Wasm.IEEE32.add (dotPrefix weights input weightOffset inputWidth outputWidth row column inputWidth)
    (word weights (biasOffset + column))

theorem linearRows_eq (weights input : ByteArray)
    (weightOffset biasOffset inputWidth outputWidth rows : Nat) :
    linearRows weights input weightOffset biasOffset inputWidth outputWidth rows =
      LeanExe.Packed.generateUInt32LE (rows * outputWidth) (fun index =>
        value weights input weightOffset biasOffset inputWidth outputWidth
          (index / outputWidth) (index % outputWidth)) := by
  unfold linearRows
  congr 1
  funext index
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  change LeanExe.Float32.addBits (dotPrefix weights input weightOffset inputWidth
    outputWidth (index / outputWidth) (index % outputWidth) inputWidth) _ = _
  exact Project.ProofKit.F32Add.add_eq _ _

#print axioms linearRows_eq

end Project.Gpt2LinearRows
