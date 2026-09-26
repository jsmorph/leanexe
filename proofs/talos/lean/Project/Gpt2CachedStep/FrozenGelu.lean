import Project.Gpt2CachedStep.ExpNeg.FrozenSpec
import Project.Gpt2CachedStep.FrozenFiniteLt
import Project.ProofKit.F32Div

namespace Project.Gpt2CachedStep.Frozen.Gelu
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2

theorem signOr_widen (value : UInt32) :
    value.toUInt64 ||| 2147483648 = (value ||| 2147483648).toUInt64 := by
  rw [UInt32.toUInt64_or]
  rfl

theorem tail_widen (value : UInt32) : 1090519040 < value.toUInt64 ↔ 1090519040 < value :=
  UInt32.toUInt64_lt (a := 1090519040) (b := value)

set_option maxRecDepth 16384 in
theorem gelu_exact (env : HostEnv Unit) (initial : Store Unit) (input : UInt32) :
    TerminatesWith env «module» 31 initial [.i64 input.toUInt64]
      (fun final values => final = initial ∧ values = [.i64 (gelu input).toUInt64]) := by
  let a := input &&& 2147483647
  let square := Wasm.IEEE32.mul a a
  let factor := Wasm.IEEE32.add (Wasm.IEEE32.mul square 1027024659) 1065353216
  let magnitude := Wasm.IEEE32.mul (Wasm.IEEE32.mul factor a) 1070350890
  have hcall := ExpNeg.Spec.expNeg_exact env initial (magnitude ||| 2147483648)
  refine TerminatesWith.of_wp_entry_for (f := func31Def) rfl ?_
  change wp «module» func31 _ initial
    { params := [.i64 input.toUInt64], locals := List.replicate 9 (.i64 0) } env
  simp only [func31]
  by_cases htail : 1090519040 < input &&& 2147483647 <;>
    by_cases hsign : input < 2147483648
  all_goals
    repeat' first
      | wp_packed_frame [List.getElem?_cons_zero, List.getElem?_cons_succ,
          FiniteLt.magnitude_widen, FiniteLt.sign_widen, signOr_widen, tail_widen, htail, hsign,
          show (2147483647 : UInt64) &&& 4294967295 = 2147483647 from rfl,
          show (2147483648 : UInt64) &&& 4294967295 = 2147483648 from rfl]
      | (refine wp_iff_cons rfl ?_
         first
         | rw [ite_eq_left (by decide)]
         | rw [ite_eq_right (by decide)])
      | (refine wp_call_tw hcall ?_
         rintro final values ⟨rfl, rfl⟩)
    simp only [func31Def, gelu, htail, hsign, reduceIte,
      F32Add.add_eq, F32Mul.mul_eq, F32Div.div_eq,
      List.length_cons, List.length_nil, List.take, List.drop]
    exact ⟨True.intro, rfl⟩

#print axioms gelu_exact

end Project.Gpt2CachedStep.Frozen.Gelu
