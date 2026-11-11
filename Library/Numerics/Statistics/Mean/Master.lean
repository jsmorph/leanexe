import Library.Numerics.Statistics.Mean.Compiled
import Library.Numerics.Reductions.Binary64
import LeanExe.Dialect.ArrayLemmas
import Verified.Master

namespace Library.Numerics.Statistics.Mean

open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096
open LeanExe.ProofKit LeanExe.ProofKit.F64Approx LeanExe.Dialect
open Library.Numerics.Reductions.Binary64 Library.Numerics.Reductions.SumError

theorem mean_export :
    ({ name := "mean", funcIdx := 2 } : Wasm.Export) ∈ compiled.module.exports := by
  decide +kernel

theorem mean_empty : Wasm.IEEE64.isNaN (mean #[]).toBits = true := by
  unfold mean
  rw [F64Bits.toBits_div, F64Convert.toBits_toFloat]
  decide +kernel

/-- The mean of `n > 0` finite floats lies within `γ_n` times the mean magnitude, plus
`2 ^ -1075` for a quotient below the normal range, of the exact mean. -/
theorem mean_spec (xs : Array Float) (hs : xs.size < 2 ^ 52) (h0 : 0 < xs.size)
    (hf : ∀ x ∈ xs, Finite x.toBits)
    (hS : (xs.toList.map fun x => |value x.toBits|).sum ≤ 2 ^ 1021) :
    Finite (mean xs).toBits ∧
      |value (mean xs).toBits - (xs.toList.map fun x => value x.toBits).sum / xs.size| ≤
        (xs.size : ℝ) / (2 ^ 53 - xs.size) *
          ((xs.toList.map fun x => |value x.toBits|).sum / xs.size) + 1 / 2 ^ 1075 := by
  have hsum := sum_raw xs.toList (fun x => x) (fun a ha => hf a (Array.mem_toList_iff.mp ha))
    (by rw [Array.length_toList]; exact hs) (hS.trans (by norm_num : (2 : ℝ) ^ 1021 ≤ 2 ^ 1022))
  beta_reduce at hsum
  rw [Array.length_toList] at hsum
  have hnf : FApprox xs.size.toUInt64.toFloat (xs.size : ℝ) 0 := by
    have := toFloat_exact xs.size.toUInt64 (by rw [size_toUInt64 xs (by omega)]; omega)
    rwa [size_toUInt64 xs (by omega)] at this
  unfold mean
  rw [← Array.foldl_toList]
  set n := xs.size
  set V := (xs.toList.map fun x => |value x.toBits|).sum
  set S := (xs.toList.map fun x => value x.toBits).sum
  set Q := (1 + 1 / 2 ^ 53 : ℝ) ^ (n - 1)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast h0
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h0
  have hQ1 : 1 ≤ Q := one_le_pow₀ (by norm_num)
  have hQ2 : Q < 2 := pow_le_two 53 (n - 1) (by
    have : ((n - 1 : ℕ) : ℝ) < 2 ^ 52 := by exact_mod_cast (Nat.sub_le _ _).trans_lt hs
    linarith)
  have hV0 : 0 ≤ V := sum_nonneg_of _ _ fun _ _ => abs_nonneg _
  have hSV : |S| ≤ V := abs_sum_le _ _
  have hQV : Q * V < 2 ^ 1022 ∨ V = 0 := by
    rcases hV0.lt_or_eq with h | h
    · left
      have : Q * V ≤ Q * 2 ^ 1021 := mul_le_mul_of_nonneg_left hS (by linarith)
      have : Q * (2 : ℝ) ^ 1021 < 2 * 2 ^ 1021 := (mul_lt_mul_iff_left₀ (by positivity)).mpr hQ2
      have : (2 : ℝ) * 2 ^ 1021 = 2 ^ 1022 := by norm_num
      linarith
    · right; exact h.symm
  have hB : (V + (Q - 1) * V) / (n - 0) ≤ Q * V / n := le_of_eq (by ring_nf)
  have hBmax : Q * V / n < 2 ^ 1022 := by
    rcases hQV with h | h
    · have : Q * V / n ≤ Q * V := div_le_self (by positivity) hn1
      linarith
    · rw [h]; norm_num
  have hd := fapprox_div hsum hnf V n hSV (by rw [abs_of_pos hnpos]) hnpos (Q * V / n) hB hBmax
  refine ⟨hd.1, hd.2.trans ?_⟩
  have hpow : (1 + 1 / 2 ^ 53 : ℝ) ^ n = (1 + 1 / 2 ^ 53) * Q := by
    rw [← pow_succ', show n - 1 + 1 = n by omega]
  have hg := gamma_pow 53 n (by
    have : (n : ℝ) < 2 ^ 52 := by exact_mod_cast hs
    linarith)
  rw [hpow] at hg
  have e : ((Q - 1) * V + V * 0 / n) / (n - 0) + Q * V / n / 2 ^ 53 =
      ((1 + 1 / 2 ^ 53) * Q - 1) * (V / n) := by
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    field_simp
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hg (div_nonneg hV0 hnpos.le)
  linarith

/-- The export `mean`, called on an array of `n` finite floats whose magnitudes sum to at most
`2 ^ 1021`, returns a NaN when `n = 0` and otherwise a finite float within
`γ_n (Σ |x_i|) / n + 2 ^ -1075` of the exact mean `(Σ x_i) / n`, where `γ_k = k / (2 ^ 53 - k)`. -/
theorem mean_master :
    Verified.Master compiled.module compiled.tables "mean" compiled.mean.bound
      (fun xs : Array Float => (∀ x ∈ xs, Finite x.toBits) ∧
        (xs.toList.map fun x => |value x.toBits|).sum ≤ 2 ^ 1021)
      (fun xs (y : Float) => (xs.size = 0 → Wasm.IEEE64.isNaN y.toBits = true) ∧
        (0 < xs.size → Finite y.toBits ∧
          |value y.toBits - (xs.toList.map fun x => value x.toBits).sum / xs.size| ≤
            (xs.size : ℝ) / (2 ^ 53 - xs.size) *
              ((xs.toList.map fun x => |value x.toBits|).sum / xs.size) + 1 / 2 ^ 1075)) :=
  .of_trapFree (.ofA compiled.mean.trapFree) nofun mean_export
    (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ h => h)
    fun _ _ _ xs ⟨_, _, hxs⟩ hD => by
      have hs : xs.size < 2 ^ 52 := by
        have := hxs.values.size_lt_memory32; simp at this; omega
      refine ⟨fun h0 => ?_, fun h0 => mean_spec xs hs h0 hD.1 hD.2⟩
      rw [Array.eq_empty_of_size_eq_zero h0]
      exact mean_empty

#print axioms mean_master

end Library.Numerics.Statistics.Mean
