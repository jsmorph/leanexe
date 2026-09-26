import Project.Gpt2CachedStep.FrozenProgram
import LeanExe.Models.Gpt2.Numerics
import Project.ProofKit.F32Add
import Project.ProofKit.F32Mul
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.Frozen.ExpPolynomial
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2

set_option maxRecDepth 16384 in
theorem expPolynomial_exact (env : HostEnv Unit) (initial : Store Unit) (value : UInt32) :
    TerminatesWith env «module» 26 initial [.i64 value.toUInt64]
      (fun final values => final = initial ∧ values = [.i64 (expPolynomial value).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func26Def) rfl ?_
  change wp «module» func26 _ initial
    { params := [.i64 value.toUInt64], locals := List.replicate 18 (.i64 0) } env
  simp only [func26]
  wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ]
  simp only [func26Def, List.length_cons, List.length_nil,
    expPolynomial, F32Add.add_eq, F32Mul.mul_eq, List.take]
  exact ⟨True.intro, rfl⟩

#print axioms expPolynomial_exact

end Project.Gpt2CachedStep.Frozen.ExpPolynomial
