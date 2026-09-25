import Project.Gpt2QuantizedCached.Program
import LeanExe.Models.Gpt2.Quantized.Kernel
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2QuantizedCached.Finite
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem finite_exact (env : HostEnv Unit) (initial : Store Unit) (value : UInt32) :
    TerminatesWith env «module» 25 initial [.i64 value.toUInt64]
      (fun final values => final = initial ∧ values = [.i64 (if finite value then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func25Def) rfl ?_
  change wp «module» func25 _ initial
    { params := [.i64 value.toUInt64], locals := [.i64 0] } env
  simp only [func25]
  have hMask : value.toUInt64 &&& 2147483647 = (value &&& 2147483647).toUInt64 := by
    rw [UInt32.toUInt64_and]
    rfl
  have hLt : value.toUInt64 &&& 2147483647 < 2139095040 ↔
      value &&& 2147483647 < 2139095040 := by
    rw [hMask]
    exact UInt32.toUInt64_lt (a := value &&& 2147483647) (b := 2139095040)
  repeat' first
    | wp_packed_frame [hMask, UInt32.toUInt64_lt,
        show (2147483647 : UInt64) &&& 4294967295 = 2147483647 from rfl]
    | (refine wp_iff_cons rfl ?_; split)
  all_goals simp_all [func25Def, finite]

#print axioms finite_exact
end Project.Gpt2QuantizedCached.Finite
