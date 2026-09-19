import Project.Gpt2CachedStep.ExpNeg.SquareStep
import Project.Gpt2CachedStep.ExpPolynomial

namespace Project.Gpt2CachedStep.ExpNeg.Spec
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2

theorem emitted_entry : func27 =
    [.constI64 3263168512, .localGet 0, .ltUI64,
      .iff 0 0 [.constI64 0, .localSet 26] branchCode, .localGet 26] := rfl

set_option maxRecDepth 16384 in
theorem expNeg_exact (env : HostEnv Unit) (initial : Store Unit) (input : UInt32) :
    TerminatesWith env «module» 27 initial [.i64 input.toUInt64]
      (fun final values => final = initial ∧ values = [.i64 (expNeg input).toUInt64]) := by
  have hcutWiden : 3263168512 < input.toUInt64 ↔ 3263168512 < input :=
    UInt32.toUInt64_lt (a := 3263168512) (b := input)
  refine TerminatesWith.of_wp_entry_for (f := func27Def) rfl ?_
  change wp «module» func27 _ initial
    { params := [.i64 input.toUInt64], locals := List.replicate 36 (.i64 0) } env
  rw [emitted_entry]
  wp_packed_frame [List.getElem?_cons_zero]
  refine wp_iff_cons rfl ?_
  by_cases hcut : 3263168512 < input
  · simp only [hcutWiden, hcut, reduceIte]
    wp_packed_frame
    simp [func27Def, expNeg_eq, hcut]
  · simp only [hcutWiden, hcut, reduceIte]
    rw [ite_eq_right (by decide)]
    rw [emitted_reduction, List.append_assoc]
    simp only [branchCode, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.take, List.cons_append, List.nil_append]
    wp_packed_frame [List.getElem?_cons_zero]
    apply RangeFoldLoop.program_spec (count := 6) (P := Reduced input)
    · decide
    · simp [RangeFoldLoop.Ready, Locals.get]
    · simp [Reduced]
    · intro index next hindex hready hacc Q rest hnext
      exact reduceStep_spec env initial input index next hindex hready hacc Q rest hnext
    · intro reduced hready hacc
      rcases hacc with ⟨hparams, hlength, hvalue, hsquares, hstride⟩
      change wp «module» (branchCode.drop 17) _ initial reduced env
      rw [emitted_squaring, List.append_assoc]
      simp only [branchCode, func27, List.getElem?_cons_zero, List.getElem?_cons_succ,
        List.drop, List.take, List.cons_append, List.nil_append]
      wp_packed_frame [hparams, hlength, hvalue, hsquares, hstride, hready.1]
      refine wp_call_tw (ExpPolynomial.expPolynomial_exact env initial (reducePrefix input 6).1) ?_
      rintro final values ⟨rfl, rfl⟩
      wp_packed_frame [hparams, hlength, hvalue, hsquares, hstride, hready.1]
      have hcount : (reducePrefix input 6).2 < UInt64.size := by
        have := reducePrefix_count input 6
        change (reducePrefix input 6).2 < 18446744073709551616
        omega
      apply RangeFoldLoop.program_spec (count := (reducePrefix input 6).2)
        (P := Squared input (expPolynomial (reducePrefix input 6).1))
      · exact hcount
      · simp [RangeFoldLoop.Ready, Locals.get, hlength]
      · simp [Squared, hlength]
      · intro index next hindex hready hacc Q rest hnext
        exact squareStep_spec env final input (expPolynomial (reducePrefix input 6).1)
          (reducePrefix input 6).2 index next hcount hindex hready hacc Q rest hnext
      · intro result hready hacc
        rcases hacc with ⟨hparams, hlength, hvalue, hstride⟩
        wp_packed_frame [hparams, hlength, hvalue, hstride, hready.1]
        simp [func27Def, expNeg_eq, hcut]

#print axioms expNeg_exact

end Project.Gpt2CachedStep.ExpNeg.Spec
