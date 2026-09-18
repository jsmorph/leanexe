import Project.Gpt2CachedStep.CachedRowMaximum.Step

namespace Project.Gpt2CachedStep.CachedRowMaximum.Spec
open Wasm Project.ProofKit PackedMemory PackedFloatFrame

set_option maxRecDepth 16384 in
theorem cachedRowMaximum_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (head size : Nat)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (head + 1) * size * 4 ≤ input.size) (hSize : 0 < size) :
    TerminatesWith env «module» 25 initial
      [.i64 (UInt64.ofNat size), .i64 (UInt64.ofNat head), .i64 (UInt64.ofNat input.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Models.Gpt2.cachedRowMaximum input head size).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func25Def) rfl ?_
  change wp «module» func25 _ initial
    { params := [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat head), .i64 (UInt64.ofNat size)],
      locals := List.replicate 42 (.i64 0), values := [] } env
  have hEnd : (head * size + size) * 4 ≤ input.size := by simpa [Nat.add_mul] using hrow
  have hProduct64 : head * size < UInt64.size := by
    have := hbytes.1
    change head * size < 18446744073709551616
    omega
  have hSize64 : size < UInt64.size := by
    have := hbytes.1
    change size < 18446744073709551616
    omega
  have hNonzero : UInt64.ofNat size ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hSize64] at this
    change size = 0 at this
    omega
  have hsafe := CheckedNatMul.guard_of_nat_fits head size hProduct64 hNonzero
  rw [emitted_loop, List.append_assoc]
  simp only [func25, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hNonzero)]
  wp_packed_frame [hNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafe)]
  wp_packed_frame
  simp only [← UInt64.ofNat_mul]
  refine wp_call_tw (PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env initial owner ptr input (head * size) hbytes (by omega)) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame
  apply RangeFoldLoop.program_spec (count := size) (P := Accumulator owner ptr input head size)
  · exact hSize64
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator, LeanExe.Models.Gpt2.word]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env final owner ptr input head size index next hbytes hrow hSize
      hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    wp_packed_frame [hparams, hlength, htotal, hready.1]
    simp [func25Def, cachedRowMaximum_eq]

#print axioms cachedRowMaximum_exact

end Project.Gpt2CachedStep.CachedRowMaximum.Spec
