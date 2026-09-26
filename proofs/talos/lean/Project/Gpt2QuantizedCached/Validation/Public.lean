import Project.Gpt2QuantizedCached.Validation.Entry

namespace Project.Gpt2QuantizedCached.Validation
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem validateModel_exact (env : HostEnv Unit) (initial : Store Unit)
    (ptr : UInt64) (weights : ByteArray)
    (hWeights : PackedMemory.ByteArrayAt initial.mem ptr.toNat weights) :
    TerminatesWith env «module» 60 initial [.i64 (UInt64.ofNat weights.size), .i64 ptr]
      (fun final values => final = initial ∧ values = [.i64 (validateModel weights)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func60Def) rfl ?_
  change wp «module» func60 _ initial
    { params := [.i64 ptr, .i64 (UInt64.ofNat weights.size)], locals := [.i64 0] } env
  simp only [func60]
  wp_packed_frame []
  refine wp_call_tw (Validation.exact env initial 0 ptr weights hWeights) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame []
  simp [func60Def]

#print axioms validateModel_exact
end Project.Gpt2QuantizedCached.Validation
