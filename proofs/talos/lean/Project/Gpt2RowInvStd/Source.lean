import LeanExe.Models.Gpt2.Kernel
import Project.ProofKit.F32Add
import Project.ProofKit.F32Sub
import Project.ProofKit.F32Mul
import Project.ProofKit.F32Div
import Project.ProofKit.F32Sqrt

namespace Project.Gpt2RowInvStd

open LeanExe.Models.Gpt2

def variancePrefix (input : ByteArray) (row : Nat) (mean : UInt32) (count : Nat) : UInt32 :=
  (List.range count).foldl (fun total index =>
    let delta := LeanExe.Float32.subBits (word input (row * 768 + index)) mean
    LeanExe.Float32.addBits total (LeanExe.Float32.mulBits delta delta)) 0

@[simp] theorem variancePrefix_zero (input : ByteArray) (row : Nat) (mean : UInt32) :
    variancePrefix input row mean 0 = 0 := rfl

theorem variancePrefix_succ (input : ByteArray) (row : Nat) (mean : UInt32) (count : Nat) :
    variancePrefix input row mean (count + 1) =
      let delta := Wasm.IEEE32.sub (word input (row * 768 + count)) mean
      Wasm.IEEE32.add (variancePrefix input row mean count) (Wasm.IEEE32.mul delta delta) := by
  simp only [variancePrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Project.ProofKit.F32Add.add_eq, Project.ProofKit.F32Sub.sub_eq,
    Project.ProofKit.F32Mul.mul_eq]

theorem rowInvStd_eq (input : ByteArray) (row : Nat) (mean : UInt32) :
    rowInvStd input row mean =
      Wasm.IEEE32.div 0x3F800000 (Wasm.IEEE32.sqrt (Wasm.IEEE32.add
        (Wasm.IEEE32.div (variancePrefix input row mean 768) 0x44400000) 0x3727C5AC)) := by
  simp only [rowInvStd, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range']
  change LeanExe.Float32.divBits _ (LeanExe.Float32.sqrtBits (LeanExe.Float32.addBits
    (LeanExe.Float32.divBits (variancePrefix input row mean 768) _) _)) = _
  rw [Project.ProofKit.F32Div.div_eq, Project.ProofKit.F32Sqrt.sqrt_eq,
    Project.ProofKit.F32Add.add_eq, Project.ProofKit.F32Div.div_eq]

end Project.Gpt2RowInvStd
