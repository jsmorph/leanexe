import Project.Gpt2CachedStep.Program
import LeanExe.Models.Gpt2.Numerics
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.FiniteLt
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2

theorem magnitude_widen (value : UInt32) :
    value.toUInt64 &&& 2147483647 = (value &&& 2147483647).toUInt64 := by
  rw [UInt32.toUInt64_and]
  rfl

theorem magnitude_zero (value : UInt32) :
    value.toUInt64 &&& 2147483647 = 0 ↔ value &&& 2147483647 = 0 := by
  rw [magnitude_widen]
  exact UInt32.toUInt64_inj (a := value &&& 2147483647) (b := 0)

theorem sign_widen (value : UInt32) : value.toUInt64 < 2147483648 ↔ value < 2147483648 :=
  UInt32.toUInt64_lt (a := value) (b := 2147483648)

theorem finiteLt_exact (env : HostEnv Unit) (initial : Store Unit) (left right : UInt32) :
    TerminatesWith env «module» 24 initial [.i64 right.toUInt64, .i64 left.toUInt64]
      (fun final values => final = initial ∧
        values = [.i64 (if finiteLt left right then 1 else 0)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func24Def) rfl ?_
  change wp «module» func24 _ initial
    { params := [.i64 left.toUInt64, .i64 right.toUInt64], locals := [.i64 0] } env
  simp only [func24]
  repeat' first
    | wp_packed_frame [*, magnitude_zero, sign_widen, UInt32.toUInt64_lt,
        show (2147483647 : UInt64) &&& 4294967295 = 2147483647 from rfl]
    | rw [ite_eq_left (by decide)]
    | rw [ite_eq_right (by decide)]
    | (refine wp_iff_cons rfl ?_
       first
       | rw [ite_eq_left (by decide)]
       | rw [ite_eq_right (by decide)]
       | split)
  all_goals simp_all [func24Def, finiteLt, magnitude_zero, sign_widen, UInt32.toUInt64_lt]
  all_goals simp_all only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le]
  all_goals split_ifs <;> omega

#print axioms finiteLt_exact

end Project.Gpt2CachedStep.FiniteLt
