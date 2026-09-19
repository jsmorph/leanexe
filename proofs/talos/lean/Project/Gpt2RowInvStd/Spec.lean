import Project.Gpt2RowInvStd.Step

namespace Project.Gpt2RowInvStd.Spec

open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

theorem rowInvStd_exact (env : HostEnv Unit) (initial : Store Unit)
    (ptr : UInt64) (input : ByteArray) (row : Nat) (mean : UInt32)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (row + 1) * 768 * 4 ≤ input.size) :
    TerminatesWith env «module» 1 initial
      [.i64 mean.toUInt64, .i64 (UInt64.ofNat row), .i64 (UInt64.ofNat input.size), .i64 ptr]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Models.Gpt2.rowInvStd input row mean).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial
    { params := [.i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat row), .i64 mean.toUInt64],
      locals := List.replicate 27 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func1, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame
  apply RangeFoldLoop.program_spec (count := 768) (P := fun index => Accumulator ptr input row index mean)
  · decide
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env initial ptr input row index mean next hbytes hrow
      hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    wp_packed_frame [hparams, hlength, htotal, hready.1]
    simp [func1Def, rowInvStd_eq]

#print axioms rowInvStd_exact

end Project.Gpt2RowInvStd.Spec
