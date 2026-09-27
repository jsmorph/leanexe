import Project.ExpArm.Rescale
import Project.ExpArm.Table
import Project.ProofKit.ArrayWordRead

namespace Project.ExpArm.Spec
open Wasm Project.ProofKit

set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def ExactSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (x : UInt64),
    UInt64Array.At initial 4096 table →
    TerminatesWith env m 2 initial [.i64 x]
      (fun final values => final = initial ∧ values = [.i64 (exp x)])

theorem exp_exact : ExactSpecFor Project.ExpArm.module := by
  intro env initial x ht
  have htrue32 : (1 : UInt32) ≠ 0 := by decide
  have htrue64 : (1 : UInt64) ≠ 0 := by decide
  have hfalse32 : ¬ (0 : UInt32) ≠ 0 := by simp
  let k := IEEE64.add (IEEE64.mul 0x40671547652B82FE x) 0x4338000000000000
  let i := (2 * (k &&& 127)).toNat
  have hk : IEEE64.add (IEEE64.mul 0x40671547652B82FE x) 0x4338000000000000 = k := rfl
  have hi : i ≤ 254 := index_bound k
  have hi0 : i < table.size := by rw [table_size]; omega
  have hi1 : i + 1 < table.size := by rw [table_size]; omega
  have hnext : (2 * (k &&& 127) + 1).toNat = i + 1 := index_next k
  have hindex0 : 2 * (k &&& 127) < (256 : UInt64) := by
    rw [UInt64.lt_iff_toNat_lt]
    change i < 256
    omega
  have hindex1 : 2 * (k &&& 127) + 1 < (256 : UInt64) := by
    rw [UInt64.lt_iff_toNat_lt, hnext]
    change i + 1 < 256
    omega
  have hadd : ¬ 2 * (k &&& 127) + 1 < 2 * (k &&& 127) := by
    rw [UInt64.lt_iff_toNat_lt, hnext]
    change ¬ i + 1 < i
    omega
  have hr0 : initial.mem.read64 4096 = 256 := ht.lengthRead
  have hp : UInt32.ofNat ((4096 : UInt64).toNat % 2^32) = 4096 := rfl
  have hb0 : ¬ (4096 : UInt32).toNat + 8 > initial.mem.pages * 65536 :=
    Nat.not_lt.mpr ht.lengthBound
  have hr1 := ht.wordElement (2 * (k &&& 127)) hi0
  have hr2 := ht.wordElement (2 * (k &&& 127) + 1) (by simpa only [hnext] using hi1)
  have hb1 := Nat.not_lt.mpr hr1.1
  have hb2 := Nat.not_lt.mpr hr2.1
  have hnanGuard : x &&& 0x7FFFFFFFFFFFFFFF ≤ 0x7FF0000000000000 ↔
      ¬ 0x7FF0000000000000 < x &&& 0x7FFFFFFFFFFFFFFF := UInt64.not_lt.symm
  refine TerminatesWith.of_wp_entry_for (f := func2Def) rfl ?_ (by decide)
  change wp Project.ExpArm.module func2 _ initial (func2Def.toLocals [.i64 x]) env
  unfold func2
  by_cases hsmall : x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000
  · repeat first
      | wp_fixed_frame [func2Def, hsmall, not_true_eq_false, not_false_eq_true, htrue32, htrue64, reduceIte]
      | rw [ite_eq_left htrue32]
      | rw [ite_eq_right hfalse32]
      | (refine wp_iff_cons rfl ?_)
    simp [exp, hsmall]
  · by_cases hbig : 0x4090000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF
    · by_cases hnan : 0x7FF0000000000000 < x &&& 0x7FFFFFFFFFFFFFFF
      all_goals by_cases hsign : x >>> 63 = 0
      all_goals
        repeat first
          | wp_fixed_frame [func2Def, hsmall, hbig, hnanGuard, hnan, hsign,
              not_true_eq_false, not_false_eq_true, htrue32, htrue64, reduceIte]
          | rw [ite_eq_left htrue32]
          | rw [ite_eq_right hfalse32]
          | (refine wp_iff_cons rfl ?_)
      all_goals simp [exp, hsmall, hbig, hnan, hsign]
    · by_cases hscale : 0x4080000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF
      all_goals
        repeat first
          | wp_fixed_frame [func2Def, hsmall, hbig, hscale, hp, hr0, hb0,
              hb1, hb2, hr1.2, hr2.2, hindex0, hindex1, hadd,
              Wasm.f64Mul, Wasm.f64Add, Wasm.f64Sub, hk,
              UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
              not_true_eq_false, not_false_eq_true, htrue32, htrue64, reduceIte]
          | (refine wp_call_tw (rescale_exact env initial _ _ _) ?_
             rintro st values ⟨hst, rfl⟩
             subst st)
          | rw [ite_eq_left htrue32]
          | rw [ite_eq_right hfalse32]
          | (refine wp_iff_cons rfl ?_)
      all_goals simp [exp, hsmall, hbig, hscale, hk, hnext, i]

#print axioms exp_exact
end Project.ExpArm.Spec
