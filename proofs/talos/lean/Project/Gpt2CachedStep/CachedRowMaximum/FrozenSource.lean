import LeanExe.Models.Gpt2.Cached

namespace Project.Gpt2CachedStep.Frozen.CachedRowMaximum
open LeanExe.Models.Gpt2

def maximumPrefix (input : ByteArray) (head size count : Nat) : UInt32 :=
  (List.range count).foldl (fun total index =>
    if finiteLt total (word input (head * size + index)) then word input (head * size + index) else total)
    (word input (head * size))

@[simp] theorem maximumPrefix_zero (input : ByteArray) (head size : Nat) :
    maximumPrefix input head size 0 = word input (head * size) := rfl

theorem maximumPrefix_succ (input : ByteArray) (head size count : Nat) :
    maximumPrefix input head size (count + 1) =
      if finiteLt (maximumPrefix input head size count) (word input (head * size + count)) then
        word input (head * size + count) else maximumPrefix input head size count := by
  simp only [maximumPrefix, List.range_succ, List.foldl_append, List.foldl_cons,
    List.foldl_nil]
  rfl

theorem cachedRowMaximum_eq (input : ByteArray) (head size : Nat) :
    cachedRowMaximum input head size = maximumPrefix input head size size := by
  have step (source : Nat) (total : UInt32) :
      (if finiteLt total (word input (head * size + source)) then
        pure (ForInStep.yield (word input (head * size + source))) else pure (ForInStep.yield total) :
        Id (ForInStep UInt32)) =
      pure (ForInStep.yield (if finiteLt total (word input (head * size + source)) then
        word input (head * size + source) else total)) := by split <;> rfl
  simp only [cachedRowMaximum, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    step, List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel_right, Nat.div_one]
  rfl

#print axioms cachedRowMaximum_eq

end Project.Gpt2CachedStep.Frozen.CachedRowMaximum
