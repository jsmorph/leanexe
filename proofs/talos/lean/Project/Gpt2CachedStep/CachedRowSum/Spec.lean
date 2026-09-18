import Project.Gpt2CachedStep.CachedRowSum.Step

namespace Project.Gpt2CachedStep.CachedRowSum.Spec
open Wasm Project.ProofKit PackedMemory PackedFloatFrame

theorem cachedRowSum_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (head size : Nat)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (head + 1) * size * 4 ≤ input.size) (hSize : 0 < size) :
    TerminatesWith env «module» 28 initial
      [.i64 (UInt64.ofNat size), .i64 (UInt64.ofNat head), .i64 (UInt64.ofNat input.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Models.Gpt2.cachedRowSum input head size).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func28Def) rfl ?_
  change wp «module» func28 _ initial
    { params := [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat head), .i64 (UInt64.ofNat size)],
      locals := List.replicate 24 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func28, List.take, List.drop, List.cons_append, List.nil_append]
  wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  apply RangeFoldLoop.program_spec (count := size) (P := Accumulator owner ptr input head size)
  · have hEnd : (head * size + size) * 4 ≤ input.size := by simpa [Nat.add_mul] using hrow
    have := hbytes.1
    change size < 18446744073709551616
    omega
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env initial owner ptr input head size index next hbytes hrow hSize
      hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    wp_packed_frame [hparams, hlength, htotal, hready.1]
    simp [func28Def, cachedRowSum_eq]

#print axioms cachedRowSum_exact

end Project.Gpt2CachedStep.CachedRowSum.Spec
