import Library.Random.SplitMix64.Compiled
import LeanExe.ProofKit.F64Bits
import LeanExe.ProofKit.F64Convert
import LeanExe.ProofKit.F64NearestDiv
import LeanExe.ProofKit.F64Magnitude
import Verified.Master

namespace Library.Random.SplitMix64

open CodeLib.IEEE64 (value Finite)
open LeanExe.ProofKit

set_option exponentiation.threshold 4096

/-- The function `next` of Vigna's SplitMix64, https://prng.di.unimi.it/splitmix64.c: the state
`x` advances by `0x9e3779b97f4a7c15`, and the output is the new state `z` after
`z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9`, `z = (z ^ (z >> 27)) * 0x94d049bb133111eb`, and
`z ^ (z >> 31)`, with arithmetic modulo `2^64`.  The pair holds the new state and the output. -/
def vignaNext (x : UInt64) : UInt64 × UInt64 :=
  let x := x + 0x9e3779b97f4a7c15
  let z := (x ^^^ (x >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  (x, z ^^^ (z >>> 31))

theorem splitMix_export :
    ({ name := "splitMix", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem unitFloat_export :
    ({ name := "unitFloat", funcIdx := 3 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

/-- The export `splitMix`, called on a state, returns the new state and the output of one step of
Vigna's SplitMix64. -/
theorem splitMix_master :
    Verified.Master compiled.module compiled.tables "splitMix" compiled.splitMix.bound
      (fun _ => True) (fun (x : UInt64) (y : UInt64 × UInt64) => y = vignaNext x) :=
  .of_trapFree (.ofA compiled.splitMix.trapFree) nofun splitMix_export (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ h => h) fun _ _ _ _ _ _ => rfl

#print axioms splitMix_master

theorem sign_of_pos {w : UInt64} (h : 0 < Wasm.IEEE64.scaledValue w) :
    Wasm.IEEE64.sign w = false := by
  cases hs : Wasm.IEEE64.sign w
  · rfl
  · simp only [Wasm.IEEE64.scaledValue, hs, ite_true] at h
    omega

/-- The word of `m · 2 ^ shift` units of `2^-1074`, for `0 < m ≤ 2^53` and `shift ≤ 2043`, is
finite, has the sign bit clear, and has the value `m · 2 ^ shift / 2 ^ 1074`. -/
theorem packed_value (m shift : Nat) (hm : 0 < m) (hm' : m ≤ 2 ^ 53) (hs : shift ≤ 2043)
    (w : UInt64)
    (hw : w = Wasm.IEEE64.roundScaledMagnitude ((m : Int) < 0) ((m : Int).natAbs * 2 ^ shift)) :
    Finite w ∧ Wasm.IEEE64.sign w = false ∧ value w = (m : ℝ) * 2 ^ shift / 2 ^ 1074 := by
  subst hw
  obtain ⟨hf, hv⟩ :=
    F64GridExact.signed_grid_packing_exact (m : Int) shift (by simpa using hm') hs
  refine ⟨hf, sign_of_pos (by rw [hv]; positivity), ?_⟩
  rw [value, hv]
  norm_num

/-- `unitFloat x` is the finite float, with the sign bit clear, whose value is
`(x >>> 11) / 2^53`. -/
theorem unitFloat_value (x : UInt64) :
    Finite (unitFloat x).toBits ∧ Wasm.IEEE64.sign (unitFloat x).toBits = false ∧
      value (unitFloat x).toBits = ((x >>> 11).toNat : ℝ) / 2 ^ 53 := by
  have hb : (9007199254740992.0 : Float).toBits = 0x4340000000000000 := by decide +kernel
  have hy : (unitFloat x).toBits =
      Wasm.IEEE64.div (Wasm.IEEE64.convertI64U (x >>> 11)) 0x4340000000000000 := by
    rw [unitFloat, F64Bits.toBits_div, F64Convert.toBits_toFloat, hb]
  rw [hy]
  have hm53 : (x >>> 11).toNat < 2 ^ 53 := by
    rw [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have := x.toNat_lt
    simp only [UInt64.reduceToNat, Nat.reduceMod]
    omega
  generalize x >>> 11 = k at hm53 ⊢
  by_cases hk : k.toNat = 0
  · have hk0 : k = 0 := UInt64.toNat_inj.mp hk
    subst hk0
    have h0 : Wasm.IEEE64.div (Wasm.IEEE64.convertI64U 0) 0x4340000000000000 = 0 := by
      decide +kernel
    rw [h0, F64Magnitude.value_zero]
    exact ⟨by unfold CodeLib.IEEE64.Finite; decide, by decide, by simp⟩
  · obtain ⟨haf, has, hav⟩ := packed_value k.toNat 1074 (Nat.pos_of_ne_zero hk) hm53.le
      (by norm_num) (Wasm.IEEE64.convertI64U k) rfl
    obtain ⟨hvf, hvs, hvv⟩ := packed_value k.toNat 1021 (Nat.pos_of_ne_zero hk) hm53.le
      (by norm_num) _ rfl
    have hbf : Finite (0x4340000000000000 : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
    have hbs : Wasm.IEEE64.sign (0x4340000000000000 : UInt64) = false := by decide
    have hbv : value (0x4340000000000000 : UInt64) = 2 ^ 53 := by
      have h : Wasm.IEEE64.scaledValue (0x4340000000000000 : UInt64) = 2 ^ 1127 := by
        decide +kernel
      rw [value, h]
      norm_num
    have hq : value (Wasm.IEEE64.convertI64U k) / value (0x4340000000000000 : UInt64) =
        (k.toNat : ℝ) / 2 ^ 53 := by
      rw [hav, hbv, mul_div_assoc, div_self (by positivity : (2 : ℝ) ^ 1074 ≠ 0), mul_one]
    have hone : (1 : ℝ) ≤ k.toNat := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk
    have hlt : (k.toNat : ℝ) < 2 ^ 53 := by exact_mod_cast hm53
    have hN := F64NearestDiv.div_nearest (Wasm.IEEE64.convertI64U k) 0x4340000000000000 haf hbf
      has hbs (by
        rw [hq]
        calc (1 : ℝ) / 2 ^ 1022 ≤ 1 / 2 ^ 53 :=
              one_div_le_one_div_of_le (by positivity) (by norm_num)
          _ ≤ (k.toNat : ℝ) / 2 ^ 53 := by gcongr)
      (by
        rw [hq, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ 53)]
        calc (k.toNat : ℝ) < 2 ^ 53 := hlt
          _ ≤ 2 ^ 1022 * 2 ^ 53 := by norm_num)
    rw [hq] at hN
    obtain ⟨hwf, hws⟩ := F64NearestNonnegative.nearest_finite _ _ hN
    have hlim : (Wasm.IEEE64.roundScaledMagnitude ((k.toNat : Int) < 0)
        ((k.toNat : Int).natAbs * 2 ^ 1021)).toNat < F64NearestNonnegative.limit := by
      simp only [CodeLib.IEEE64.Finite, Wasm.IEEE64.isFinite, Wasm.IEEE64.exponent, bne_iff_ne,
        ne_eq] at hvf
      simp only [Wasm.IEEE64.sign, decide_eq_false_iff_not, not_le] at hvs
      unfold F64NearestNonnegative.limit
      omega
    have hvy : value (Wasm.IEEE64.roundScaledMagnitude ((k.toNat : Int) < 0)
        ((k.toNat : Int).natAbs * 2 ^ 1021)) = (k.toNat : ℝ) / 2 ^ 53 := by
      rw [hvv, show (2 : ℝ) ^ 1074 = 2 ^ 1021 * 2 ^ 53 by norm_num, ← div_div,
        mul_div_cancel_right₀ _ (by positivity : (2 : ℝ) ^ 1021 ≠ 0)]
    have hle := hN.2 _ hlim
    rw [hvy, sub_self, abs_zero] at hle
    exact ⟨hwf, hws, sub_eq_zero.mp (abs_nonpos_iff.mp hle)⟩

/-- The export `unitFloat`, called on a word `x`, returns the finite float, with the sign bit
clear, whose value is `(x >>> 11) / 2^53`, a multiple of `2^-53` in `[0, 1)`. -/
theorem unitFloat_master :
    Verified.Master compiled.module compiled.tables "unitFloat" compiled.unitFloat.bound
      (fun _ => True)
      (fun (x : UInt64) (y : Float) => Finite y.toBits ∧ Wasm.IEEE64.sign y.toBits = false ∧
        value y.toBits = ((x >>> 11).toNat : ℝ) / 2 ^ 53) :=
  .of_trapFree (.ofA compiled.unitFloat.trapFree) nofun unitFloat_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h) fun _ _ _ x _ _ => unitFloat_value x

#print axioms unitFloat_master

end Library.Random.SplitMix64
