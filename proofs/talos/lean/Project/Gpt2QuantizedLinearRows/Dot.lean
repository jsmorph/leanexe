import Project.Gpt2QuantizedLinearRows.DotStep

namespace Project.Gpt2QuantizedLinearRows
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized Dot

theorem dot_exact (env : HostEnv Unit) (initial : Store Unit)
    (weightOwner weightPtr inputOwner inputPtr : UInt64) (weights input : ByteArray)
    (weightOffset inputOffset width : Nat)
    (hweights : ByteArrayAt initial.mem weightPtr.toNat weights)
    (hinput : ByteArrayAt initial.mem inputPtr.toNat input)
    (hweightSize : weightOffset + width ≤ weights.size)
    (hinputSize : inputOffset + width ≤ input.size) :
    TerminatesWith env «module» 4 initial
      [.i64 (UInt64.ofNat width), .i64 (UInt64.ofNat inputOffset),
        .i64 (UInt64.ofNat weightOffset), .i64 (UInt64.ofNat input.size),
        .i64 inputPtr, .i64 inputOwner, .i64 (UInt64.ofNat weights.size),
        .i64 weightPtr, .i64 weightOwner]
      (fun final values => final = initial ∧
        values = [.i64 (dot weights input weightOffset inputOffset width).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func4Def) rfl ?_
  change wp «module» func4 _ initial
    { params := [.i64 weightOwner, .i64 weightPtr, .i64 (UInt64.ofNat weights.size),
        .i64 inputOwner, .i64 inputPtr, .i64 (UInt64.ofNat input.size),
        .i64 (UInt64.ofNat weightOffset), .i64 (UInt64.ofNat inputOffset),
        .i64 (UInt64.ofNat width)],
      locals := List.replicate 23 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func4, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame []
  apply RangeFoldLoop.program_spec (count := width)
    (P := Accumulator weightOwner weightPtr inputOwner inputPtr weights input weightOffset inputOffset width)
  · have := hinput.1
    change width < 18446744073709551616
    omega
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env initial weightOwner weightPtr inputOwner inputPtr weights input
      weightOffset inputOffset width index next hweights hinput hweightSize hinputSize
      hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    wp_packed_frame [hparams, hlength, htotal, hready.1]
    simp [func4Def]

#print axioms dot_exact

end Project.Gpt2QuantizedLinearRows
