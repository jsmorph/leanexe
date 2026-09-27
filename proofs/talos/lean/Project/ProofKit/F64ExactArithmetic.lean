import Project.ProofKit.F64RoundingScale
import Project.ProofKit.F64DyadicBounds
import CodeLib.IEEE64.Operations

namespace Project.ProofKit.F64ExactArithmetic
open CodeLib.IEEE64

set_option exponentiation.threshold 4096

theorem roundShift_exact (n shift : Nat) (hs : 0 < shift) (hd : 2^shift ∣ n) :
    Wasm.IEEE32.roundShift n shift = n / 2^shift := by
  have hh : 0 < 2^shift / 2 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : shift ≠ 0)
    simp [pow_succ]
  simp [Wasm.IEEE32.roundShift, Nat.mod_eq_zero_of_dvd hd, hh]

theorem roundedMagnitude_mul_power (n k : Nat) (hn : n < 2^53) :
    roundedMagnitude (n * 2^k) = n * 2^k := by
  by_cases hsmall : n * 2^k < 2^53
  · simp only [roundedMagnitude, hsmall, ite_true]
  have hn0 : n ≠ 0 := by intro h; simp [h] at hsmall
  have hlog : Nat.log2 n < 53 := (Nat.log2_lt hn0).mpr hn
  have hprod := F64DyadicBounds.log2_mul_two_pow n k hn0
  let shift := Nat.log2 (n * 2^k) - 52
  have hs : 0 < shift := by
    have h := (Nat.le_log2 (Nat.mul_ne_zero hn0 (by positivity))).mpr
      (Nat.le_of_not_gt hsmall)
    dsimp [shift]
    omega
  have hsk : shift ≤ k := by dsimp [shift]; omega
  have hd : 2^shift ∣ n * 2^k := by
    have he : n * 2^k = (n * 2^(k-shift)) * 2^shift := by
      rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hsk]
    rw [he]
    exact dvd_mul_left _ _
  rw [F64Packing.roundedMagnitude_eq_shift _ (by omega)]
  change Wasm.IEEE32.roundShift (n * 2^k) shift * 2^shift = _
  rw [roundShift_exact _ _ hs hd]
  exact Nat.div_mul_cancel hd

theorem pack_exact (negative : Bool) (n k : Nat) (hn : n < 2^53)
    (hmax : n * 2^k < 2^2097) :
    Finite (Wasm.IEEE64.roundScaledMagnitude negative (n * 2^k)) ∧
    Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.roundScaledMagnitude negative (n * 2^k)) =
      n * 2^k ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundScaledMagnitude negative (n * 2^k)) = negative := by
  have h := F64Packing.pack_spec negative (n * 2^k) hmax
  rwa [roundedMagnitude_mul_power n k hn] at h

theorem dyadic_mul_power (negative : Bool) (n base k : Nat) (hn : n < 2^53) :
    Wasm.IEEE64.roundDyadicMagnitude negative (n * 2^(base+k)) base =
      Wasm.IEEE64.roundScaledMagnitude negative (n * 2^k) := by
  by_cases hn0 : n = 0
  · subst n
    simp only [Nat.zero_mul]
    cases negative <;> rfl
  have hp : n * 2^(base+k) ≠ 0 := Nat.mul_ne_zero hn0 (by positivity)
  have hlog : Nat.log2 n < 53 := (Nat.log2_lt hn0).mpr hn
  have hprod := F64DyadicBounds.log2_mul_two_pow n (base+k) hn0
  let j := Nat.log2 (n * 2^(base+k)) - (base+52)
  have hj : j ≤ k := by dsimp [j]; omega
  have hsplit : n * 2^(base+k) = (n * 2^(k-j)) * 2^(base+j) := by
    rw [Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  have hrestore : (n * 2^(k-j)) * 2^j = n * 2^k := by
    rw [Nat.mul_assoc, ← pow_add, Nat.sub_add_cancel hj]
  simp only [Wasm.IEEE64.roundDyadicMagnitude, beq_iff_eq, hp, ite_false]
  change Wasm.IEEE64.roundScaledMagnitude negative
    (if j = 0 then if base = 0 then n * 2^(base+k)
      else Wasm.IEEE32.roundShift (n * 2^(base+k)) base
    else Wasm.IEEE32.roundShift (n * 2^(base+k)) (base+j) * 2^j) = _
  by_cases hj0 : j = 0
  · rw [ite_eq_left hj0]
    by_cases hb : base = 0
    · simp [hb]
    · rw [ite_eq_right hb]
      have hnbase : n * 2^(base+k) = (n * 2^k) * 2^base := by
        rw [pow_add]
        ring
      rw [hnbase, F64DyadicBounds.roundShift_mul_two_pow _ _ (by omega)]
  · rw [ite_eq_right hj0, hsplit,
      F64DyadicBounds.roundShift_mul_two_pow _ _ (by omega), hrestore]

theorem signed_pack_exact (z : Int) (n k : Nat) (hn : n < 2^53)
    (hz : z.natAbs = n * 2^k) (hmax : n * 2^k < 2^2097) :
    Finite (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) ∧
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude (z < 0) z.natAbs) = z := by
  have h := pack_exact (z < 0) n k hn hmax
  rw [hz]
  refine ⟨h.1, ?_⟩
  rw [Wasm.IEEE64.scaledValue, h.2.1, h.2.2]
  simp only [decide_eq_true_eq, ← hz]
  split
  · rename_i hs
    exact (Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hs)).symm
  · rename_i hs
    exact (Int.eq_natAbs_of_nonneg (Int.le_of_not_gt hs)).symm

theorem add_exact_scaled (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (n k : Nat) (hn : n < 2^53)
    (hz : (Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b).natAbs = n * 2^k)
    (hmax : n * 2^k < 2^2097) :
    Finite (Wasm.IEEE64.add a b) ∧
    Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) =
      Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b := by
  let z := Wasm.IEEE64.scaledValue a + Wasm.IEEE64.scaledValue b
  by_cases hz0 : z = 0
  · have h := add_relative_spec a b ha hb (by change z.natAbs < 2^1076; simp [hz0])
    refine ⟨h.1, ?_⟩
    have he := h.2
    change |Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) - z| * (2^53 : Int) ≤ z.natAbs at he
    simp only [hz0, Int.natAbs_zero, sub_zero] at he
    change Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b) = z
    rw [hz0]
    apply abs_eq_zero.mp
    have hp := abs_nonneg (Wasm.IEEE64.scaledValue (Wasm.IEEE64.add a b))
    omega
  · have h := signed_pack_exact z n k hn hz hmax
    simpa [Wasm.IEEE64.add, not_nan_of_finite ha, not_nan_of_finite hb,
      not_infinite_of_finite ha, not_infinite_of_finite hb, z, hz0] using h

theorem mul_exact_scaled (a b : UInt64) (ha : Finite a) (hb : Finite b)
    (n k : Nat) (hn : n < 2^53)
    (hp : Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b =
      n * 2^(1074+k)) (hmax : n * 2^k < 2^2097) :
    Finite (Wasm.IEEE64.mul a b) ∧
    value (Wasm.IEEE64.mul a b) = value a * value b := by
  have he : Wasm.IEEE64.mul a b = Wasm.IEEE64.roundScaledMagnitude
      (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) (n * 2^k) := by
    rw [mul_finite_rounder a b ha hb, hp, dyadic_mul_power _ n 1074 k hn]
  have hr := pack_exact (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) n k hn hmax
  have hm : Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul a b) * 2^1074 =
      Wasm.IEEE64.scaledMagnitude a * Wasm.IEEE64.scaledMagnitude b := by
    rw [he, hr.2.1, hp, Nat.mul_assoc, ← pow_add]
    congr 2
    omega
  have hs : Wasm.IEEE64.sign (Wasm.IEEE64.mul a b) =
      (Wasm.IEEE64.sign a != Wasm.IEEE64.sign b) := by rw [he, hr.2.2]
  have hi : Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul a b) * (2 : Int)^1074 =
      Wasm.IEEE64.scaledValue a * Wasm.IEEE64.scaledValue b := by
    have hm' : (Wasm.IEEE64.scaledMagnitude (Wasm.IEEE64.mul a b) : Int) * 2^1074 =
        (Wasm.IEEE64.scaledMagnitude a : Int) * Wasm.IEEE64.scaledMagnitude b := by
      exact_mod_cast hm
    simp only [Wasm.IEEE64.scaledValue, hs]
    cases Wasm.IEEE64.sign a <;> cases Wasm.IEEE64.sign b <;>
      simp only [Bool.bne_false, Bool.bne_true, Bool.not_false, Bool.not_true,
        Bool.false_eq_true, ite_false, ite_true] <;> nlinarith only [hm']
  refine ⟨by rw [he]; exact hr.1, ?_⟩
  have hi' : (Wasm.IEEE64.scaledValue (Wasm.IEEE64.mul a b) : ℝ) * (2 : ℝ)^1074 =
      (Wasm.IEEE64.scaledValue a : ℝ) * Wasm.IEEE64.scaledValue b := by
    exact_mod_cast hi
  simp only [value, div_mul_div_comm]
  rw [← hi']
  field_simp

#print axioms pack_exact
#print axioms dyadic_mul_power
#print axioms add_exact_scaled
#print axioms mul_exact_scaled
end Project.ProofKit.F64ExactArithmetic
