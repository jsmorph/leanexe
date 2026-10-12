import LeanExe.ProofKit.F64AddBounds
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Magnitude
import LeanExe.IR.Combinators

namespace LeanExe.ProofKit.F64SequentialSum
open CodeLib.IEEE64

theorem loop_sum_bound (n : UInt64) (terms : UInt64 → Float) (bounds : Nat → ℝ)
    (hfinite : ∀ j, j < n.toNat → Finite (terms (UInt64.ofNat j)).toBits)
    (hnonneg : ∀ j, j < n.toNat → 0 ≤ bounds j)
    (hterms : ∀ j, j < n.toNat →
      |value (terms (UInt64.ofNat j)).toBits| ≤ bounds j)
    (hsafe : (1 + unitRoundoff64) ^ n.toNat *
      (∑ j ∈ Finset.range n.toNat, bounds j) < (2 : ℝ) ^ 1023) :
    Finite (LeanExe.loop n (0.0 : Float) (fun j acc => acc + terms j)).toBits ∧
    |value (LeanExe.loop n (0.0 : Float) (fun j acc => acc + terms j)).toBits -
      (∑ j ∈ Finset.range n.toNat, value (terms (UInt64.ofNat j)).toBits)| ≤
      ((1 + unitRoundoff64) ^ n.toNat - 1) *
        (∑ j ∈ Finset.range n.toNat, bounds j) ∧
    |value (LeanExe.loop n (0.0 : Float) (fun j acc => acc + terms j)).toBits| ≤
      (1 + unitRoundoff64) ^ n.toNat *
        (∑ j ∈ Finset.range n.toNat, bounds j) := by
  let q : ℝ := 1 + unitRoundoff64
  let B (k : Nat) : ℝ := ∑ j ∈ Finset.range k, bounds j
  let S (k : Nat) : ℝ := ∑ j ∈ Finset.range k, value (terms (UInt64.ofNat j)).toBits
  have hu : 0 ≤ unitRoundoff64 := by norm_num [unitRoundoff64]
  have hq : 1 ≤ q := by dsimp [q]; linarith
  have hq0 : 0 ≤ q := zero_le_one.trans hq
  have hB0 (k : Nat) (hk : k ≤ n.toNat) : 0 ≤ B k := by
    apply Finset.sum_nonneg
    intro j hj
    exact hnonneg j (lt_of_lt_of_le (Finset.mem_range.mp hj) hk)
  have hBmono (k l : Nat) (hkl : k ≤ l) (hl : l ≤ n.toNat) : B k ≤ B l := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hkl)
    intro j hj _
    exact hnonneg j (lt_of_lt_of_le (Finset.mem_range.mp hj) hl)
  have hzero : (0.0 : Float).toBits = 0 := by rfl
  apply LeanExe.IR.loop_induction (P := fun k (acc : Float) =>
    Finite acc.toBits ∧
    |value acc.toBits - S k| ≤ (q ^ k - 1) * B k ∧
    |value acc.toBits| ≤ q ^ k * B k)
  · simp only [hzero, F64Magnitude.value_zero, S, B, Finset.range_zero,
      Finset.sum_empty, abs_zero, pow_zero, sub_self, mul_zero,
      le_refl, and_true]
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  · intro k acc hk hacc
    have hk1 : k + 1 ≤ n.toNat := by omega
    have hBk10 := hB0 (k + 1) hk1
    have hBk : B k ≤ B (k + 1) := hBmono k (k + 1) (by omega) hk1
    have hpow : 1 ≤ q ^ k := one_le_pow₀ hq
    have hpowN : q ^ k ≤ q ^ n.toNat := pow_le_pow_right₀ hq (by omega)
    have hBsucc : B (k + 1) = B k + bounds k := by
      exact Finset.sum_range_succ bounds k
    have hSsucc : S (k + 1) = S k + value (terms (UInt64.ofNat k)).toBits := by
      exact Finset.sum_range_succ _ k
    have hexact : |value acc.toBits + value (terms (UInt64.ofNat k)).toBits| ≤
        q ^ k * B (k + 1) := by
      calc
        _ ≤ |value acc.toBits| + |value (terms (UInt64.ofNat k)).toBits| := abs_add_le _ _
        _ ≤ q ^ k * B k + bounds k := add_le_add hacc.2.2 (hterms k hk)
        _ ≤ q ^ k * B (k + 1) := by
          rw [hBsucc]
          have hb := mul_le_mul_of_nonneg_right hpow (hnonneg k hk)
          nlinarith only [hb]
    have hexactSafe : |value acc.toBits + value (terms (UInt64.ofNat k)).toBits| <
        (2 : ℝ) ^ 1023 := by
      apply lt_of_le_of_lt hexact
      apply lt_of_le_of_lt
        (mul_le_mul hpowN (hBmono (k + 1) n.toNat hk1 le_rfl)
          hBk10 (pow_nonneg hq0 _))
      exact hsafe
    have hadd := F64AddBounds.add_real_relative acc.toBits
      (terms (UInt64.ofNat k)).toBits hacc.1 (hfinite k hk) hexactSafe
    rw [← F64Bits.toBits_add] at hadd
    have herr : |value (acc + terms (UInt64.ofNat k)).toBits -
        (value acc.toBits + value (terms (UInt64.ofNat k)).toBits)| ≤
        unitRoundoff64 * (q ^ k * B (k + 1)) :=
      hadd.2.trans (mul_le_mul_of_nonneg_left hexact hu)
    refine ⟨hadd.1, ?_, ?_⟩
    · calc
        |value (acc + terms (UInt64.ofNat k)).toBits - S (k + 1)| =
            |(value (acc + terms (UInt64.ofNat k)).toBits -
              (value acc.toBits + value (terms (UInt64.ofNat k)).toBits)) +
              (value acc.toBits - S k)| := by rw [hSsucc]; congr 1; ring
        _ ≤ |value (acc + terms (UInt64.ofNat k)).toBits -
              (value acc.toBits + value (terms (UInt64.ofNat k)).toBits)| +
              |value acc.toBits - S k| := abs_add_le _ _
        _ ≤ unitRoundoff64 * (q ^ k * B (k + 1)) + (q ^ k - 1) * B k :=
          add_le_add herr hacc.2.1
        _ ≤ unitRoundoff64 * (q ^ k * B (k + 1)) + (q ^ k - 1) * B (k + 1) :=
          add_le_add_right (mul_le_mul_of_nonneg_left hBk (sub_nonneg.mpr hpow)) _
        _ = (q ^ (k + 1) - 1) * B (k + 1) := by rw [pow_succ]; dsimp [q]; ring
    · calc
        |value (acc + terms (UInt64.ofNat k)).toBits| =
            |(value (acc + terms (UInt64.ofNat k)).toBits -
              (value acc.toBits + value (terms (UInt64.ofNat k)).toBits)) +
              (value acc.toBits + value (terms (UInt64.ofNat k)).toBits)| := by
          congr 1; ring
        _ ≤ |value (acc + terms (UInt64.ofNat k)).toBits -
              (value acc.toBits + value (terms (UInt64.ofNat k)).toBits)| +
              |value acc.toBits + value (terms (UInt64.ofNat k)).toBits| := abs_add_le _ _
        _ ≤ unitRoundoff64 * (q ^ k * B (k + 1)) + q ^ k * B (k + 1) :=
          add_le_add herr hexact
        _ = q ^ (k + 1) * B (k + 1) := by rw [pow_succ]; dsimp [q]; ring

#print axioms loop_sum_bound

end LeanExe.ProofKit.F64SequentialSum
