import Project.Gpt2QuantizedLinearRows.RowScaleStep

namespace Project.Gpt2QuantizedLinearRows
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2 RowScale

theorem rowScale_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (offset width : Nat)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hsize : (offset + width) * 4 ≤ input.size) :
    TerminatesWith env «module» 1 initial
      [.i64 (UInt64.ofNat width), .i64 (UInt64.ofNat offset),
        .i64 (UInt64.ofNat input.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (Quantized.rowScale input offset width).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial
    { params := [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size),
        .i64 (UInt64.ofNat offset), .i64 (UInt64.ofNat width)],
      locals := List.replicate 28 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func1, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame []
  apply RangeFoldLoop.program_spec (count := width)
    (P := Accumulator owner ptr input offset width)
  · have := hbytes.1
    change width < 18446744073709551616
    omega
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env initial owner ptr input offset width index next hbytes hsize
      hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    by_cases hz : maximumPrefix input offset width = 0
    · have hz64 : (maximumPrefix input offset width).toUInt64 = 0 := by rw [hz]; rfl
      wp_packed_frame [hparams, hlength, htotal, hready.1, hz64]
      iterate 3
        refine wp_iff_cons rfl ?_
        rw [ite_eq_left (by decide)]
        wp_packed_frame [hparams, hlength, htotal, hready.1, hz64]
      simp [func1Def, rowScale_eq, hz]
    · have hz64 : (maximumPrefix input offset width).toUInt64 ≠ 0 := by
        intro h
        apply hz
        apply UInt32.toNat.inj
        have := congrArg UInt64.toNat h
        simpa using this
      wp_packed_frame [hparams, hlength, htotal, hready.1, hz64]
      iterate 3
        refine wp_iff_cons rfl ?_
        first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
        wp_packed_frame [hparams, hlength, htotal, hready.1, hz64]
      have hfloor : (8388608 : UInt64) = (8388608 : UInt32).toUInt64 := rfl
      have hdivisor : UInt32.ofNat ((1123942400 : UInt64).toNat % 2^32) = 1123942400 := rfl
      simp only [hfloor, widen_lt, hdivisor]
      by_cases hf : Wasm.IEEE32.div (maximumPrefix input offset width) 1123942400 < 8388608
      all_goals
        refine wp_iff_cons rfl ?_
        simp only [hf, ↓reduceIte]
        first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
        wp_packed_frame [hparams, hlength, htotal, hready.1]
        simp [func1Def, rowScale_eq, hz, hf]

#print axioms rowScale_exact

end Project.Gpt2QuantizedLinearRows
