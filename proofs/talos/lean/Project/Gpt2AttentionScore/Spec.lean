import Project.Gpt2AttentionScore.Step

namespace Project.Gpt2AttentionScore.Spec

open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

set_option maxRecDepth 16384 in
theorem attentionScore_exact (env : HostEnv Unit) (initial : Store Unit)
    (ptr : UInt64) (input : ByteArray) (target source head : Nat)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (htarget : (target + 1) * 2304 * 4 ≤ input.size)
    (hsource : (source + 1) * 2304 * 4 ≤ input.size) (hhead : head < 12) :
    TerminatesWith env «module» 1 initial
      [.i64 (UInt64.ofNat head), .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat target),
        .i64 (UInt64.ofNat input.size), .i64 ptr]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Models.Gpt2.attentionScore input target source head).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial
    { params := [.i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat target),
        .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat head)],
      locals := List.replicate 38 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func1, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame
  apply RangeFoldLoop.program_spec (count := 64) (P := Accumulator ptr input target source head)
  · decide
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env initial ptr input target source head index next hbytes
      htarget hsource hhead hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    wp_packed_frame [hparams, hlength, htotal, hready.1]
    simp [func1Def, attentionScore_eq]

#print axioms attentionScore_exact

end Project.Gpt2AttentionScore.Spec
