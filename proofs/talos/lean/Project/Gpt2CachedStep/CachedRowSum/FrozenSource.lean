import LeanExe.Models.Gpt2.Cached
import Project.ProofKit.F32Add

namespace Project.Gpt2CachedStep.Frozen.CachedRowSum
open LeanExe.Models.Gpt2

def sumPrefix (input : ByteArray) (head size count : Nat) : UInt32 :=
  (List.range count).foldl (fun total index =>
    LeanExe.Float32.addBits total (word input (head * size + index))) 0

@[simp] theorem sumPrefix_zero (input : ByteArray) (head size : Nat) :
    sumPrefix input head size 0 = 0 := rfl

theorem sumPrefix_succ (input : ByteArray) (head size count : Nat) :
    sumPrefix input head size (count + 1) =
      Wasm.IEEE32.add (sumPrefix input head size count) (word input (head * size + count)) := by
  simp only [sumPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil, Project.ProofKit.F32Add.add_eq]

theorem cachedRowSum_eq (input : ByteArray) (head size : Nat) :
    cachedRowSum input head size = sumPrefix input head size size := by
  simp only [cachedRowSum, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel_right, Nat.div_one]
  rfl

#print axioms cachedRowSum_eq

end Project.Gpt2CachedStep.Frozen.CachedRowSum
