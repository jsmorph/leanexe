import Project.Gpt2QuantizedLinearRows.Source
import Project.ProofKit.F32Div

namespace Project.Gpt2QuantizedLinearRows
open LeanExe.Models.Gpt2 LeanExe.Models.Gpt2.Quantized Project.ProofKit

def maximumPrefix (input : ByteArray) (offset count : Nat) : UInt32 :=
  (List.range count).foldl (fun current index =>
    let magnitude := word input (offset + index) &&& 0x7FFFFFFF
    if current < magnitude then magnitude else current) 0

@[simp] theorem maximumPrefix_zero (input : ByteArray) (offset : Nat) :
    maximumPrefix input offset 0 = 0 := rfl

theorem maximumPrefix_succ (input : ByteArray) (offset count : Nat) :
    maximumPrefix input offset (count + 1) =
      if maximumPrefix input offset count < (word input (offset + count) &&& 0x7FFFFFFF) then
        word input (offset + count) &&& 0x7FFFFFFF else maximumPrefix input offset count := by
  simp only [maximumPrefix, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

theorem maximum_yield (current magnitude : UInt32) :
    (if current < magnitude then pure (ForInStep.yield magnitude) else pure (ForInStep.yield current) :
      Id (ForInStep UInt32)) =
      pure (ForInStep.yield (if current < magnitude then magnitude else current)) := by
  split <;> rfl

theorem rowScale_eq (input : ByteArray) (offset width : Nat) :
    rowScale input offset width =
      if maximumPrefix input offset width = 0 then 0x3F800000
      else let scale := Wasm.IEEE32.div (maximumPrefix input offset width) 0x42FE0000
        if scale < 0x00800000 then 0x00800000 else scale := by
  simp only [rowScale, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ← List.range_eq_range', Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  simp_rw [maximum_yield]
  rw [List.forIn_pure_yield_eq_foldl]
  change (if maximumPrefix input offset width == 0 then _ else _) = _
  simp only [beq_iff_eq, F32Div.div_eq]
  rfl

#print axioms rowScale_eq

end Project.Gpt2QuantizedLinearRows
