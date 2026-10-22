import Library.Numerics.Float64.Exp.ExpCoreInterval
import LeanExe.ProofKit.F64NearestBinade

namespace Library.Numerics.Float64.Exp.ExpCoreOneStep
open CodeLib.IEEE64
open LeanExe.ProofKit F64NearestNonnegative F64NearestEven F64NearestBinade

set_option exponentiation.threshold 4096

private theorem exponent_bounds (q : Int) (hq : -769 ≤ q ∧ q ≤ 768) :
    let e := (q + 1023).toNat
    2 ≤ e ∧ e + 2 < 2047 ∧ (e : Int) = q + 1023 := by
  dsimp only
  omega

private theorem gap_exponents (e : Nat) (q : Int) (he : 2 ≤ e)
    (heq : (e : Int) = q + 1023) :
    ((e - 1 : Nat) : Int) = q + 1074 - 52 ∧
      (((e - 1) - 1 : Nat) : Int) = q + 1074 - 53 := by
  omega

theorem core_one_step (x : UInt64) (hxf : Finite x) (hx : |value x| ≤ 512) :
    let w := roundNearestEven (Real.exp (value x))
    (ExpCoreBounds.core x).toNat ≤ w.toNat + 1 ∧
      w.toNat ≤ (ExpCoreBounds.core x).toNat + 1 := by
  obtain ⟨k, q, j, hkv, hk, _, _, hs, _, _⟩ := ExpCoreState.reduction_state x hxf hx
  have hq := ExpCoreInterval.quotient_bounds x k q j hxf hx hkv hk
  let e := (q + 1023).toNat
  obtain ⟨he2, heh, heq⟩ := exponent_bounds q hq
  change 2 ≤ e at he2
  change e + 2 < 2047 at heh
  change (e : Int) = q + 1023 at heq
  have hgexp := gap_exponents e q he2 heq
  have hf := (ExpCoreBounds.core_error x hxf hx).1
  have hw := (roundNearestEven_spec (Real.exp (value x))).1
  have hupper : value (UInt64.ofNat ((e + 1) * 2 ^ 52)) = 2 * (2 : ℝ) ^ q := by
    calc
      _ = (2 : ℝ) ^ (q + 1) := boundary_power (e + 1) (q + 1) (by omega)
        (by omega) (by push_cast; omega)
      _ = _ := by rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]; ring
  by_cases hj : j.val = 0
  · have hI := ExpCoreInterval.zero_interval x k q j hxf hx hkv hk hj hs
    have hlower : value (UInt64.ofNat ((e - 1) * 2 ^ 52)) = (2 : ℝ) ^ q / 2 := by
      calc
        _ = (2 : ℝ) ^ (q - 1) := boundary_power (e - 1) (q - 1) (by omega)
          (by omega) (by omega)
        _ = _ := by
          rw [sub_eq_add_neg, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
            zpow_neg, zpow_one]
          ring
    have hgap : (2 : ℝ) ^ ((e - 1) - 1) / (2 : ℝ) ^ 1074 =
        unitRoundoff64 * (2 : ℝ) ^ q := by
      rw [power_quotient_split ((e - 1) - 1) 53 q hgexp.2]
      norm_num [unitRoundoff64]
      ring
    apply one_step_normal_interval (Real.exp (value x)) (ExpCoreBounds.core x)
      (roundNearestEven (Real.exp (value x))) (e - 1) (e + 1)
      (by omega) (by omega) (by omega) (by omega) hf hw
    · rw [hlower, hupper]
      exact ⟨hI.1, hI.2.1⟩
    · rw [hlower, hupper]
      exact ⟨hI.2.2.1, hI.2.2.2.1⟩
    · rw [hgap]
      exact hI.2.2.2.2
  · have hI := ExpCoreInterval.nonzero_interval x k q j hxf hx hkv hk hj hs
    have hlower : value (UInt64.ofNat (e * 2 ^ 52)) = (2 : ℝ) ^ q :=
      boundary_power e q (by omega) (by omega) heq
    have hgap : (2 : ℝ) ^ (e - 1) / (2 : ℝ) ^ 1074 =
        2 * unitRoundoff64 * (2 : ℝ) ^ q := by
      rw [power_quotient_split (e - 1) 52 q hgexp.1]
      norm_num [unitRoundoff64]
      ring
    apply one_step_normal_interval (Real.exp (value x)) (ExpCoreBounds.core x)
      (roundNearestEven (Real.exp (value x))) e (e + 1)
      (by omega) (by omega) (by omega) heh hf hw
    · rw [hlower, hupper]
      exact ⟨hI.1, hI.2.1⟩
    · rw [hlower, hupper]
      exact ⟨hI.2.2.1, hI.2.2.2.1⟩
    · rw [hgap]
      nlinarith only [hI.2.2.2.2]

theorem expCore_one_step (x : Float) (hxf : Finite x.toBits) (hx : |value x.toBits| ≤ 512) :
    let w := roundNearestEven (Real.exp (value x.toBits))
    (Exp.expCore Exp.expTable x false).toBits.toNat ≤ w.toNat + 1 ∧
      w.toNat ≤ (Exp.expCore Exp.expTable x false).toBits.toNat + 1 := by
  obtain ⟨_, _, j, _, _, ht, hsf, _, _, _⟩ :=
    ExpCoreState.reduction_state x.toBits hxf hx
  have htf : Finite (ExpCoreState.tailBits x.toBits) := by
    rw [ht]
    exact (ExpTableBounds.entry_bounds j).2.1
  rw [ExpCoreBounds.core_bits x hsf htf]
  exact core_one_step x.toBits hxf hx

#print axioms core_one_step
#print axioms expCore_one_step

end Library.Numerics.Float64.Exp.ExpCoreOneStep
