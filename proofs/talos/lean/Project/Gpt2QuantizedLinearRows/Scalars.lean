import Project.Gpt2QuantizedLinearRows.Program
import LeanExe.Models.Gpt2.Quantized.Kernel
import Project.ProofKit.F32Div
import Project.ProofKit.F32Mul
import Project.ProofKit.F32TruncSat
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2QuantizedLinearRows
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem rescale_exact (env : HostEnv Unit) (initial : Store Unit)
    (accumulator inputScale weightScale : UInt32) :
    TerminatesWith env «module» 6 initial
      [.i64 weightScale.toUInt64, .i64 inputScale.toUInt64, .i64 accumulator.toUInt64]
      (fun final values => final = initial ∧
        values = [.i64 (rescale accumulator inputScale weightScale).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func6Def) rfl ?_
  change wp «module» func6 _ initial
    { params := [.i64 accumulator.toUInt64, .i64 inputScale.toUInt64, .i64 weightScale.toUInt64],
      locals := List.replicate 2 (.i64 0) } env
  simp only [func6]
  wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ]
  simp only [func6Def, List.length_cons, List.length_nil, rescale,
    F32Mul.mul_eq, F32Convert.ofInt32Bits_eq, List.take]
  exact ⟨True.intro, rfl⟩

#print axioms rescale_exact

theorem quantizeValue_exact (env : HostEnv Unit) (initial : Store Unit) (value scale : UInt32) :
    TerminatesWith env «module» 2 initial [.i64 scale.toUInt64, .i64 value.toUInt64]
      (fun final values => final = initial ∧ values = [.i64 (quantizeValue value scale).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_
  change wp «module» func2 _ initial
    { params := [.i64 value.toUInt64, .i64 scale.toUInt64], locals := List.replicate 4 (.i64 0) } env
  simp only [func2]
  wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ]
  have hm : (2147483647 : UInt64) = (2147483647 : UInt32).toUInt64 := rfl
  have hc : (1123942400 : UInt64) = (1123942400 : UInt32).toUInt64 := rfl
  simp only [hm, hc, mask, widen_and, widen_lt]
  by_cases h : (Wasm.IEEE32.div value scale &&& 2147483647) > 1123942400
  all_goals
    refine wp_iff_cons rfl ?_
    simp only [h, ↓reduceIte]
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ,
      show (2147483648 : UInt64) = (2147483648 : UInt32).toUInt64 from rfl,
      hc, widen_and, widen_or, narrow_byte]
    simp only [func2Def, List.length_cons, List.length_nil, quantizeValue,
      F32Div.div_eq, F32Nearest.nearest_eq, F32TruncSat.toInt32Bits_eq, h, ↓reduceIte, List.take]
    exact ⟨True.intro, rfl⟩

#print axioms quantizeValue_exact

end Project.Gpt2QuantizedLinearRows
