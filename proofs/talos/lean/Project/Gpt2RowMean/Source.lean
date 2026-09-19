import LeanExe.Models.Gpt2.Kernel
import Project.ProofKit.F32Add
import Project.ProofKit.F32Div

namespace Project.Gpt2RowMean

open LeanExe.Models.Gpt2

def sumPrefix (input : ByteArray) (row count : Nat) : UInt32 :=
  (List.range count).foldl (fun total index =>
    LeanExe.Float32.addBits total (word input (row * 768 + index))) 0

@[simp] theorem sumPrefix_zero (input : ByteArray) (row : Nat) :
    sumPrefix input row 0 = 0 := rfl

theorem sumPrefix_succ (input : ByteArray) (row count : Nat) :
    sumPrefix input row (count + 1) =
      Wasm.IEEE32.add (sumPrefix input row count) (word input (row * 768 + count)) := by
  simp only [sumPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Project.ProofKit.F32Add.add_eq]

theorem rowMean_eq (input : ByteArray) (row : Nat) :
    rowMean input row = Wasm.IEEE32.div (sumPrefix input row 768) 0x44400000 := by
  simp only [rowMean, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range']
  change LeanExe.Float32.divBits (sumPrefix input row 768) _ = _
  exact Project.ProofKit.F32Div.div_eq _ _

end Project.Gpt2RowMean
