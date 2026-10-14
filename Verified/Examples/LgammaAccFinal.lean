import Verified.Examples.LgammaApprox
import Verified.Examples.TgammaAccPath
import LeanExe.ProofKit.F64RoundNearest

/-!
**The last step of `Lgamma.accurate`**: the sum `fh + fl`, rounded once, or the value of the table
of hard cases at `x` when the rounding test of the code fails.  An error of `fh + fl` within
`ρ |log |Γ x||` with `ρ ≤ 1/(2^53 + 1)` puts the rounded sum within one step (`sum_within`).  A row `(x, f, δ)` of
`Lgamma.dbTable` holds a double `f` within `2^-60` relative of `log |Γ x|` (`LgammaApprox.DbFact`)
and a correction `δ` with `|δ| ≤ |f|/2^54`, so `f + δ` is within one step as well (`db_entry`).
`final_step` joins the two cases of the code's final `if`.
-/

namespace Verified.Examples.LgammaAccFinal
open CodeLib.IEEE64 LeanExe.ProofKit PolyBound GammaBasic LgammaApprox
open Verified.Examples.Lgamma

set_option exponentiation.threshold 4096

theorem database_cases (x f : Float) :
    database dbTable x f = f ∨ ∃ k < 19, (Tgamma.entry dbTable (3 * UInt64.ofNat k) == x) = true ∧
      database dbTable x f =
        Tgamma.entry dbTable (3 * UInt64.ofNat k + 1) +
          Tgamma.entry dbTable (3 * UInt64.ofNat k + 2) :=
  TgammaAccPath.loop_pick (fun k => Tgamma.entry dbTable (3 * k) == x)
    (fun k => Tgamma.entry dbTable (3 * k + 1) + Tgamma.entry dbTable (3 * k + 2)) f 19
    (by norm_num)

theorem db_index : ∀ k < 19, (3 * UInt64.ofNat k).toNat = 3 * k ∧
    (3 * UInt64.ofNat k + 1).toNat = 3 * k + 1 ∧ (3 * UInt64.ofNat k + 2).toNat = 3 * k + 2 := by
  decide

/-- The checks of row `k` of the table: finite words, `|δ| ≤ |f|/2^54`, and `1/16 ≤ |f| ≤ 16`. -/
def rowOk (k : ℕ) : Bool :=
  Wasm.IEEE64.isFinite dbTable[3 * k]! && Wasm.IEEE64.isFinite dbTable[3 * k + 1]! &&
    Wasm.IEEE64.isFinite dbTable[3 * k + 2]! &&
    decide (|q dbTable (3 * k + 2)| * 2 ^ 54 ≤ |q dbTable (3 * k + 1)|) &&
    decide (1 / 16 ≤ |q dbTable (3 * k + 1)|) && decide (|q dbTable (3 * k + 1)| ≤ 16)

theorem rows_ok : ∀ k < 19, rowOk k = true := by
  decide +kernel

/-- `fh + fl` within one step of `L` when its error is at most `ρ |L|` with
`ρ ≤ 1/(2^53 + 1)`. -/
theorem sum_within (fh fl : Float) (hfh : Finite fh.toBits) (hfl : Finite fl.toBits) (L : ℝ)
    (hL1 : 1 / 2 ^ 1000 ≤ |L|) (hL2 : |L| ≤ 2 ^ 1020) (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hρ : ρ ≤ 1 / (2 ^ 53 + 1)) (h : |L - (value fh.toBits + value fl.toBits)| ≤ ρ * |L|) :
    F64SignedRounding.WithinSteps 1 L (fh + fl).toBits := by
  set A := value fh.toBits + value fl.toBits with hA
  have hL0 : 0 < |L| := lt_of_lt_of_le (by positivity) hL1
  have hAL : |A - L| ≤ ρ * |L| := by rw [abs_sub_comm]; exact h
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ (by norm_num)
  have hρL : ρ * |L| < |L| := by nlinarith
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, zero_sub, abs_neg] at hAL
    linarith
  have hAt : |A| < 2 ^ 1023 := by
    have := abs_sub_abs_le_abs_sub A L
    linarith [(by norm_num : (2 : ℝ) ^ 1020 * 2 < 2 ^ 1023)]
  have hR := F64RoundNearest.add_rounded fh.toBits fl.toBits hfh hfl hA0 hAt
  rw [← F64Bits.toBits_add] at hR
  exact F64RoundNearest.within_one_of_rounded_rel _ A L hR ρ hρ0 hρ hAL
    (le_trans (by norm_num) hL1) (lt_of_le_of_lt hL2 (by norm_num))

/-- **A row of the table** within one step of `log |Γ|` at its argument. -/
theorem db_entry (wx wf wd : UInt64) (hff : Wasm.IEEE64.isFinite wf = true)
    (hfd : Wasm.IEEE64.isFinite wd = true)
    (hd : |ratOfWord wd| * 2 ^ 54 ≤ |ratOfWord wf|) (hf1 : 1 / 16 ≤ |ratOfWord wf|)
    (hf2 : |ratOfWord wf| ≤ 16)
    (hL : |lgamma (value wx) - value wf| ≤ 1 / 2 ^ 60 * |value wf|) :
    F64SignedRounding.WithinSteps 1 (lgamma (value wx))
      (Float.ofBits wf + Float.ofBits wd).toBits := by
  have hbf : (Float.ofBits wf).toBits = wf := TgammaWords.ofBits_bits wf hff
  have hbd : (Float.ofBits wd).toBits = wd := TgammaWords.ofBits_bits wd hfd
  have hwf : Finite wf := hbf ▸ TgammaWords.ofBits_finite wf hff
  have hwd : Finite wd := hbd ▸ TgammaWords.ofBits_finite wd hfd
  have hdr : |value wd| * 2 ^ 54 ≤ |value wf| := by
    have h := (Rat.cast_le (K := ℝ)).mpr hd
    push_cast at h
    rwa [ratOfWord_cast, ratOfWord_cast] at h
  have hf1r : 1 / 16 ≤ |value wf| := by
    have h := (Rat.cast_le (K := ℝ)).mpr hf1
    push_cast at h
    rwa [ratOfWord_cast] at h
  have hf2r : |value wf| ≤ 16 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hf2
    push_cast at h
    rwa [ratOfWord_cast] at h
  rw [F64Bits.toBits_add, hbf, hbd]
  set f := value wf with hfdef
  set d := value wd with hddef
  set L := lgamma (value wx) with hLdef
  have hfL : |f| * (1 - 1 / 2 ^ 60) ≤ |L| := by
    have := abs_sub_abs_le_abs_sub f L
    rw [abs_sub_comm f L] at this
    linarith
  have hLf : |L| ≤ |f| * (1 + 1 / 2 ^ 60) := by
    have := abs_sub_abs_le_abs_sub L f
    linarith
  have hS : |f + d - L| ≤ (1 / 2 ^ 54 + 1 / 2 ^ 58) * |L| := by
    have h1 : |f + d - L| ≤ |d| + |L - f| := by
      have := abs_add_le d (f - L)
      rw [abs_sub_comm f L] at this
      rwa [show f + d - L = d + (f - L) by ring]
    have h2 : |d| ≤ |f| / 2 ^ 54 := by rw [le_div_iff₀ (by positivity)]; exact hdr
    have h3 : (1 / 2 ^ 54 + 1 / 2 ^ 60) * |f| ≤ (1 / 2 ^ 54 + 1 / 2 ^ 58) * |L| := by
      have := mul_le_mul_of_nonneg_left hfL (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 54 + 1 / 2 ^ 58)
      nlinarith [abs_nonneg f]
    linarith
  have hS0 : f + d ≠ 0 := by
    intro h0
    have hdf : |d| = |f| := by rw [show d = -f by linarith, abs_neg]
    rw [hdf] at hdr
    linarith
  have hSt : |f + d| < 2 ^ 1023 := by
    have := abs_add_le f d
    have : |d| ≤ |f| := by nlinarith [abs_nonneg d]
    linarith [(by norm_num : (32 : ℝ) < 2 ^ 1023)]
  have hR := F64RoundNearest.add_rounded wf wd hwf hwd hS0 hSt
  exact F64RoundNearest.within_one_of_rounded_rel _ (f + d) L hR (1 / 2 ^ 54 + 1 / 2 ^ 58)
    (by positivity) (by norm_num) hS
    (by nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 16 * (1 - 1 / 2 ^ 60))])
    (by nlinarith [(by norm_num : (16 : ℝ) * (1 + 1 / 2 ^ 60) < 2 ^ 1022)])

/-- **The last step**: `fh + fl`, or the table's value at a hard case, within one step of
`log |Γ x|`. -/
theorem final_step (hDb : DbFact) (x : Float) (hx : Finite x.toBits) (c : Prop) [Decidable c]
    (fh fl : Float) (hfh : Finite fh.toBits) (hfl : Finite fl.toBits)
    (hL1 : 1 / 2 ^ 1000 ≤ |lgamma (value x.toBits)|) (hL2 : |lgamma (value x.toBits)| ≤ 2 ^ 1020)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / (2 ^ 53 + 1))
    (h : |lgamma (value x.toBits) - (value fh.toBits + value fl.toBits)| ≤
      ρ * |lgamma (value x.toBits)|) :
    F64SignedRounding.WithinSteps 1 (lgamma (value x.toBits))
      (if c then database dbTable x (fh + fl) else fh + fl).toBits := by
  have hsum := sum_within fh fl hfh hfl _ hL1 hL2 ρ hρ0 hρ h
  split_ifs
  · rcases database_cases x (fh + fl) with h1 | ⟨k, hk, hck, h1⟩
    · rw [h1]
      exact hsum
    · rw [h1]
      obtain ⟨i0, i1, i2⟩ := db_index k hk
      have hr := rows_ok k hk
      simp only [rowOk, Bool.and_eq_true, decide_eq_true_eq] at hr
      obtain ⟨⟨⟨⟨⟨hfx, hff⟩, hfd⟩, hd⟩, hf1⟩, hf2⟩ := hr
      have hef : Finite (Tgamma.entry dbTable (3 * UInt64.ofNat k)).toBits := by
        unfold Tgamma.entry
        rw [i0]
        exact TgammaWords.ofBits_finite _ hfx
      have hv := (F64UpperWord.float_beq_iff _ _ hef hx).mp hck
      rw [← hv]
      unfold Tgamma.entry
      rw [i0, i1, i2, TgammaWords.ofBits_bits _ hfx]
      have hk' := hDb k hk
      unfold dbX dbF q at hk'
      rw [ratOfWord_cast, ratOfWord_cast] at hk'
      exact db_entry _ _ _ hff hfd hd hf1 hf2 hk'
  · exact hsum

end Verified.Examples.LgammaAccFinal
