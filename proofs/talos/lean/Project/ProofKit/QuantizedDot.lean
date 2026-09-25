import LeanExe.Models.Gpt2.Quantized.Kernel
import Project.ProofKit.QuantizedInt32

namespace Project.ProofKit.QuantizedDot
open LeanExe.Models.Gpt2.Quantized LeanExe.Signed32 QuantizedInt32

theorem dot_eq_wordPrefix (weights input : ByteArray) (weightOffset inputOffset width : Nat) :
    dot weights input weightOffset inputOffset width =
      wordPrefix (fun i => extend8Bits input[inputOffset + i]!.toUInt32)
        (fun i => extend8Bits weights[weightOffset + i]!.toUInt32) width := by
  simp only [dot, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    List.forIn_pure_yield_eq_foldl, ← List.range_eq_range', Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rfl

@[simp] theorem dot_zero (weights input : ByteArray) (weightOffset inputOffset : Nat) :
    dot weights input weightOffset inputOffset 0 = 0 := by
  rw [dot_eq_wordPrefix]
  rfl

theorem dot_succ (weights input : ByteArray) (weightOffset inputOffset width : Nat) :
    dot weights input weightOffset inputOffset (width + 1) =
      dot weights input weightOffset inputOffset width +
        extend8Bits input[inputOffset + width]!.toUInt32 *
          extend8Bits weights[weightOffset + width]!.toUInt32 := by
  simp only [dot_eq_wordPrefix, wordPrefix, List.range_succ, List.foldl_append,
    List.foldl_cons, List.foldl_nil]

theorem dot_exact (weights input : ByteArray) (weightOffset inputOffset width : Nat)
    (hw : width ≤ 3072)
    (inputValid : ∀ i < width, input[inputOffset + i]! ≠ 128)
    (weightsValid : ∀ i < width, weights[weightOffset + i]! ≠ 128) :
    decode (dot weights input weightOffset inputOffset width) =
      sumPrefix (fun i => decode (extend8Bits input[inputOffset + i]!.toUInt32))
        (fun i => decode (extend8Bits weights[weightOffset + i]!.toUInt32)) width := by
  rw [dot_eq_wordPrefix]
  exact wordPrefix_exact _ _ width hw
    (fun i hi => byte_range _ (inputValid i hi))
    (fun i hi => byte_range _ (weightsValid i hi))

theorem dot_prefix_range (weights input : ByteArray) (weightOffset inputOffset width : Nat)
    (hw : width ≤ 3072)
    (inputValid : ∀ i < width, input[inputOffset + i]! ≠ 128)
    (weightsValid : ∀ i < width, weights[weightOffset + i]! ≠ 128) :
    |decode (dot weights input weightOffset inputOffset width)| ≤ (width : Int) * 16129 := by
  rw [dot_exact weights input weightOffset inputOffset width hw inputValid weightsValid]
  exact prefix_bound _ _ width
    (fun i hi => byte_range _ (inputValid i hi))
    (fun i hi => byte_range _ (weightsValid i hi))

#print axioms dot_exact
#print axioms dot_prefix_range

end Project.ProofKit.QuantizedDot
