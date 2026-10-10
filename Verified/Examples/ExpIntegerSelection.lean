import LeanExe.ProofKit.F64RoundingScale
import LeanExe.ProofKit.F64PackingModel
import Verified.Examples.ExpReductionExact

namespace Verified.Examples.ExpIntegerSelection
open CodeLib.IEEE64
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

theorem packing_integer_binade (n : Nat) (hl : 2 ^ 1126 ≤ n) (hu : n < 2 ^ 1127) :
    Finite (Wasm.IEEE64.roundScaledMagnitude false n) ∧
    Wasm.IEEE64.sign (Wasm.IEEE64.roundScaledMagnitude false n) = false ∧
    ∃ q : Nat,
      Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude false n) =
        (q : Int) * 2 ^ 1074 ∧
      |(q : ℝ) - (n : ℝ) / (2 : ℝ) ^ 1074| ≤ 1 / 2 := by
  have hn : n ≠ 0 := by omega
  have h53 : 2 ^ 53 ≤ n := (by norm_num : (2 : Nat) ^ 53 ≤ 2 ^ 1126).trans hl
  have hmax : n < 2 ^ 2097 := hu.trans_le (by norm_num)
  have hlog : Nat.log2 n = 1126 := (Nat.log2_eq_iff hn).mpr ⟨hl, hu⟩
  let q := Wasm.IEEE32.roundShift n 1074
  have hr : roundedMagnitude n = q * 2 ^ 1074 := by
    simpa only [hlog, show 1126 - 52 = 1074 by decide] using
      F64Packing.roundedMagnitude_eq_shift n h53
  have hp := F64Packing.pack_spec false n hmax
  have hv : Wasm.IEEE64.scaledValue (Wasm.IEEE64.roundScaledMagnitude false n) =
      (q : Int) * 2 ^ 1074 := by
    simp only [Wasm.IEEE64.scaledValue, hp.2.1, hp.2.2, hr,
      Bool.false_eq_true, ite_false, Int.natCast_mul, Int.natCast_pow, Nat.cast_ofNat]
  have he : |(q : ℝ) * (2 : ℝ) ^ 1074 - (n : ℝ)| ≤ (2 : ℝ) ^ 1074 / 2 := by
    simpa only [hr, hlog, show 1126 - 52 = 1074 by decide,
      Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using F64Packing.roundedMagnitude_error n
  refine ⟨hp.1, hp.2.2, q, hv, ?_⟩
  have hid : (q : ℝ) - (n : ℝ) / (2 : ℝ) ^ 1074 =
      ((q : ℝ) * (2 : ℝ) ^ 1074 - (n : ℝ)) / (2 : ℝ) ^ 1074 := by
    field_simp
  rw [hid, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ 1074)]
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ 1074)).mpr
  calc
    _ ≤ (2 : ℝ) ^ 1074 / 2 := he
    _ = (1 / 2) * (2 : ℝ) ^ 1074 := by ring

#print axioms packing_integer_binade


def shifted (z : UInt64) : UInt64 := Wasm.IEEE64.add z 0x4338000000000000

theorem magic_values :
    Finite 0x4338000000000000 ∧ Wasm.IEEE64.sign 0x4338000000000000 = false ∧
    Wasm.IEEE64.scaledValue 0x4338000000000000 = (3 : Int) * 2 ^ 1125 ∧
    value 0x4338000000000000 = (3 : ℝ) * 2 ^ 51 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold CodeLib.IEEE64.Finite
    decide +kernel
  · decide +kernel
  · norm_num [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign,
      Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  · norm_num [value, Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude,
      Wasm.IEEE64.sign, Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]

theorem shifted_sum_binade (z : UInt64) (hz : |value z| ≤ (2 : ℝ) ^ 18) :
    (2 : Int) ^ 1126 ≤ Wasm.IEEE64.scaledValue z + Wasm.IEEE64.scaledValue 0x4338000000000000 ∧
    Wasm.IEEE64.scaledValue z + Wasm.IEEE64.scaledValue 0x4338000000000000 <
      (2 : Int) ^ 1127 := by
  have hp : 0 < (2 : ℝ) ^ 1074 := by positivity
  have hzr : |(Wasm.IEEE64.scaledValue z : ℝ)| ≤ (2 : ℝ) ^ 1092 := by
    rw [value, abs_div, abs_of_pos hp] at hz
    calc
      _ ≤ (2 : ℝ) ^ 18 * (2 : ℝ) ^ 1074 := (div_le_iff₀ hp).mp hz
      _ = (2 : ℝ) ^ 1092 := by rw [← pow_add]
  have hzi : |Wasm.IEEE64.scaledValue z| ≤ (2 : Int) ^ 1092 := by exact_mod_cast hzr
  have hb := abs_le.mp hzi
  rw [magic_values.2.2.1]
  norm_num at hb ⊢
  constructor <;> omega

theorem shifted_integer (z : UInt64) (hzf : Finite z) (hz : |value z| ≤ (2 : ℝ) ^ 18) :
    Finite (shifted z) ∧ Wasm.IEEE64.sign (shifted z) = false ∧
    ∃ q : Nat, Wasm.IEEE64.scaledValue (shifted z) = (q : Int) * 2 ^ 1074 ∧
      |(q : ℝ) - (value z + value 0x4338000000000000)| ≤ 1 / 2 := by
  let S := Wasm.IEEE64.scaledValue z + Wasm.IEEE64.scaledValue 0x4338000000000000
  have hb := shifted_sum_binade z hz
  have hSpos : 0 < S := lt_of_lt_of_le (by norm_num) hb.1
  have hS0 : S ≠ 0 := ne_of_gt hSpos
  have hSn : ¬S < 0 := not_lt_of_ge hSpos.le
  dsimp only [S] at hS0 hSn
  have hcast : (S.natAbs : Int) = S := (Int.eq_natAbs_of_nonneg hSpos.le).symm
  have hl : 2 ^ 1126 ≤ S.natAbs := by
    have h : (2 : Int) ^ 1126 ≤ (S.natAbs : Int) := by rw [hcast]; exact hb.1
    exact_mod_cast h
  have hu : S.natAbs < 2 ^ 1127 := by
    have h : (S.natAbs : Int) < (2 : Int) ^ 1127 := by rw [hcast]; exact hb.2
    exact_mod_cast h
  have hm := magic_values.1
  have ha : shifted z = Wasm.IEEE64.roundScaledMagnitude false S.natAbs := by
    simp [shifted, Wasm.IEEE64.add, not_nan_of_finite hzf, not_nan_of_finite hm,
      not_infinite_of_finite hzf, not_infinite_of_finite hm, S, hS0, hSn]
  obtain ⟨hf, hs, q, hv, he⟩ := packing_integer_binade S.natAbs hl hu
  have hcastR : (S.natAbs : ℝ) = (S : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun x : Int => (x : ℝ)) hcast
  have hd : (S.natAbs : ℝ) / (2 : ℝ) ^ 1074 =
      value z + value 0x4338000000000000 := by
    rw [hcastR]
    simp only [S, Int.cast_add, value, add_div]
  rw [ha]
  exact ⟨hf, hs, q, hv, by simpa only [hd] using he⟩

#print axioms magic_values
#print axioms shifted_sum_binade
#print axioms shifted_integer


def selected (z : UInt64) : UInt64 := Wasm.IEEE64.sub (shifted z) 0x4338000000000000

private theorem selected_pack (z : UInt64) (q : Nat) (hf : Finite (shifted z))
    (hs : Wasm.IEEE64.sign (shifted z) = false)
    (hv : Wasm.IEEE64.scaledValue (shifted z) = (q : Int) * 2 ^ 1074) :
    let k := (q : Int) - 3 * 2 ^ 51
    selected z = Wasm.IEEE64.roundScaledMagnitude (k < 0) (k.natAbs * 2 ^ 1074) := by
  let k := (q : Int) - 3 * 2 ^ 51
  change selected z = Wasm.IEEE64.roundScaledMagnitude (k < 0) (k.natAbs * 2 ^ 1074)
  have hneg : Wasm.IEEE64.negate 0x4338000000000000 = 0xC338000000000000 := by
    decide +kernel
  have hnf : Finite 0xC338000000000000 := by
    unfold CodeLib.IEEE64.Finite
    decide +kernel
  have hnv : Wasm.IEEE64.scaledValue 0xC338000000000000 = -(3 : Int) * 2 ^ 1125 := by
    norm_num [Wasm.IEEE64.scaledValue, Wasm.IEEE64.scaledMagnitude, Wasm.IEEE64.sign,
      Wasm.IEEE64.exponent, Wasm.IEEE64.fraction, UInt64.toNat_ofNat]
  have hsum : Wasm.IEEE64.scaledValue (shifted z) +
      Wasm.IEEE64.scaledValue 0xC338000000000000 = k * 2 ^ 1074 := by
    rw [hv, hnv, show (2 : Int) ^ 1125 = 2 ^ 51 * 2 ^ 1074 by rw [← pow_add]]
    dsimp [k]
    ring
  have ha : selected z =
      if k * (2 : Int) ^ 1074 = 0 then 0
      else Wasm.IEEE64.roundScaledMagnitude (k * (2 : Int) ^ 1074 < 0)
        (k * (2 : Int) ^ 1074).natAbs := by
    simp [selected, Wasm.IEEE64.sub, hneg, Wasm.IEEE64.add,
      not_nan_of_finite hf, not_nan_of_finite hnf, not_infinite_of_finite hf,
      not_infinite_of_finite hnf, hs, hsum]
  rw [ha]
  by_cases hk0 : k = 0
  · rw [hk0]
    simp only [zero_mul, Int.natAbs_zero]
    decide +kernel
  · have hd : 0 < (2 : Int) ^ 1074 := by positivity
    have hnz : k * (2 : Int) ^ 1074 ≠ 0 := mul_ne_zero hk0 hd.ne'
    have hni : k * (2 : Int) ^ 1074 < 0 ↔ k < 0 := by
      constructor
      · intro h
        by_contra hk
        exact (not_lt_of_ge (mul_nonneg (le_of_not_gt hk) hd.le)) h
      · intro hk
        have hm := mul_pos (neg_pos.mpr hk) hd
        nlinarith only [hm]
    have habs : (k * (2 : Int) ^ 1074).natAbs = k.natAbs * 2 ^ 1074 := by
      rw [Int.natAbs_mul]
      norm_num
    simp only [ite_eq_right hnz, hni, habs]

theorem selected_integer_of_shifted (z : UInt64) (q : Nat)
    (hf : Finite (shifted z)) (hs : Wasm.IEEE64.sign (shifted z) = false)
    (hv : Wasm.IEEE64.scaledValue (shifted z) = (q : Int) * 2 ^ 1074)
    (he : |(q : ℝ) - (value z + value 0x4338000000000000)| ≤ 1 / 2)
    (hz : |value z| ≤ (2 : ℝ) ^ 18) :
    let k := (q : Int) - 3 * 2 ^ 51
    Finite (selected z) ∧ Wasm.IEEE64.scaledValue (selected z) = k * 2 ^ 1074 ∧
      k.natAbs ≤ 2 ^ 18 ∧ |(k : ℝ) - value z| ≤ 1 / 2 := by
  let k := (q : Int) - 3 * 2 ^ 51
  have hke : |(k : ℝ) - value z| ≤ 1 / 2 := by
    have hid : (k : ℝ) - value z =
        (q : ℝ) - (value z + value 0x4338000000000000) := by
      dsimp [k]
      simp only [Int.cast_sub, Int.cast_natCast, Int.cast_ofNat, magic_values.2.2.2]
      ring
    rw [hid]
    exact he
  have hkm : |(k : ℝ)| ≤ (2 : ℝ) ^ 18 + 1 / 2 := by
    calc
      _ = |((k : ℝ) - value z) + value z| := by rw [sub_add_cancel]
      _ ≤ |(k : ℝ) - value z| + |value z| := abs_add_le _ _
      _ ≤ 1 / 2 + (2 : ℝ) ^ 18 := add_le_add hke hz
      _ = (2 : ℝ) ^ 18 + 1 / 2 := by ring
  have habsR : |(k : ℝ)| = (k.natAbs : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    norm_num
  have hk2R : (2 : ℝ) * (k.natAbs : ℝ) ≤ 2 * (2 : ℝ) ^ 18 + 1 := by
    rw [← habsR]
    linarith only [hkm]
  have hk2 : 2 * k.natAbs ≤ 2 * (2 : Nat) ^ 18 + 1 := by exact_mod_cast hk2R
  have hk : k.natAbs ≤ 2 ^ 18 := by omega
  have hp := ExpReductionExact.integer_packing_exact k hk
  refine ⟨?_, ?_, hk, hke⟩
  · rw [selected_pack z q hf hs hv]
    exact hp.1
  · rw [selected_pack z q hf hs hv]
    exact hp.2

theorem selected_integer (z : UInt64) (hzf : Finite z) (hz : |value z| ≤ (2 : ℝ) ^ 18) :
    ∃ k : Int, Finite (selected z) ∧
      Wasm.IEEE64.scaledValue (selected z) = k * 2 ^ 1074 ∧
      k.natAbs ≤ 2 ^ 18 ∧ |(k : ℝ) - value z| ≤ 1 / 2 := by
  obtain ⟨hf, hs, q, hv, he⟩ := shifted_integer z hzf hz
  exact ⟨(q : Int) - 3 * 2 ^ 51, selected_integer_of_shifted z q hf hs hv he hz⟩

#print axioms selected_integer_of_shifted

#print axioms selected_integer

end Verified.Examples.ExpIntegerSelection
