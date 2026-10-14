import Verified.Examples.ErfcSeries
import Verified.Examples.ErfcRound
import Verified.Examples.ErfcCast
import LeanExe.ProofKit.RatExpLog
import LeanExe.ProofKit.RealErfScaled
import LeanExe.ProofKit.F64NearestSteps

/-!
The tables of hard cases of `Erfc`.  `hardCase_cases`: `Erfc.hardCase` returns its fallback or
the rounded sum of the two words of a row whose input equals `x`.  For such a row the result is a
fixed word, which the kernel computes, and one step follows from a rational enclosure of `erfc`
at the row's input (`hard_within`, from `F64NearestSteps.within_of_interior`).  The enclosures
come from the series of `erf` (`erf_encl`) and, for the asymptotic rows, from a model of
`erfcxN` and an enclosure of `exp (-x²)` by `RatExpLog.abs_exp_sub_le` at `-x²/1024` followed by
ten squarings (`exp_chain`).  `half_within` (from `F64NearestSteps.within_of_half`) serves a row
whose value lies too close to the start of its binade for `hard_within`.
-/

namespace Verified.Examples.ErfcHardBase

open Real Set CodeLib.IEEE64 LeanExe.ProofKit ErfcOps ErfcRound ErfcSeries PolyBound PolyCalc RealErf
  RealErfScaled F64NearestNonnegative

set_option exponentiation.threshold 4096

theorem fold_cases (g : ℕ → Float) (c : ℕ → Bool) (f : Float) : ∀ m : ℕ,
    Nat.fold m (fun i _ acc => if c i = true then g i else acc) f = f ∨
      ∃ k < m, c k = true ∧ Nat.fold m (fun i _ acc => if c i = true then g i else acc) f = g k
  | 0 => Or.inl (by simp)
  | m + 1 => by
    rw [Nat.fold_succ]
    by_cases h : c m = true
    · right
      exact ⟨m, by omega, h, by simp only [h, if_true]⟩
    · simp only [h, Bool.false_eq_true, if_false]
      rcases fold_cases g c f m with h1 | ⟨k, hk, hc, he⟩
      · exact Or.inl h1
      · exact Or.inr ⟨k, by omega, hc, he⟩

/-- `Erfc.hardCase` returns its fallback or the sum of a row whose input equals `x`. -/
theorem hardCase_cases (tab : Array UInt64) (o n : UInt64) (x f : Float) :
    Erfc.hardCase tab o n x f = f ∨ ∃ k < n.toNat,
      (Erfc.entry tab (o + 3 * UInt64.ofNat k) == x) = true ∧
      Erfc.hardCase tab o n x f = Erfc.entry tab (o + 3 * UInt64.ofNat k + 1) +
        Erfc.entry tab (o + 3 * UInt64.ofNat k + 2) := by
  unfold Erfc.hardCase LeanExe.loop
  exact fold_cases (fun i => Erfc.entry tab (o + 3 * UInt64.ofNat i + 1) +
    Erfc.entry tab (o + 3 * UInt64.ofNat i + 2))
    (fun i => Erfc.entry tab (o + 3 * UInt64.ofNat i) == x) f n.toNat

/-- `erf q` between rational bounds from the series of `n` terms. -/
theorem erf_encl (n : ℕ) (q : ℚ) (hq : 0 ≤ q) (hS : 0 ≤ evalQ (ser n) q) :
    ((sLo * evalQ (ser n) q - sHi * serRem n q : ℚ) : ℝ) ≤ erf q ∧
      erf q ≤ ((sHi * evalQ (ser n) q + sHi * serRem n q : ℚ) : ℝ) := by
  have h := erf_ser n (q : ℝ) q (le_of_eq (abs_of_nonneg (by qc hq)))
  have hqv : eval (ser n) (q : ℝ) = (evalQ (ser n) q : ℝ) := (PolyCalc.evalQ_cast _ _).symm
  rw [hqv] at h
  have hS' : (0 : ℝ) ≤ evalQ (ser n) q := by qc hS
  have hR : (0 : ℝ) ≤ serRem n q := by
    have : (0 : ℚ) ≤ serRem n q := by unfold serRem; positivity
    qc this
  have h1 := scale_lo
  have h2 := scale_hi
  have k1 : (sLo : ℝ) * evalQ (ser n) q ≤ scale * evalQ (ser n) q :=
    mul_le_mul_of_nonneg_right h1 hS'
  have k2 : scale * evalQ (ser n) q ≤ (sHi : ℝ) * evalQ (ser n) q :=
    mul_le_mul_of_nonneg_right h2 hS'
  have k3 : scale * (serRem n q : ℝ) ≤ (sHi : ℝ) * serRem n q := mul_le_mul_of_nonneg_right h2 hR
  push_cast
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

/-- The enclosures of `exp (2^m q)` by squaring: `expSum q N ± expRem N` at the start. -/
def ChainOK (q : ℚ) (N : ℕ) (los his : List ℚ) (m : ℕ) : Prop :=
  |q| ≤ 1 ∧ 0 < N ∧ los.getD 0 0 ≤ RatExpLog.expSum q N - RatExpLog.expRem N ∧
    RatExpLog.expSum q N + RatExpLog.expRem N ≤ his.getD 0 0 ∧
    ∀ i < m, 0 ≤ los.getD i 0 ∧ los.getD (i + 1) 0 ≤ los.getD i 0 ^ 2 ∧
      his.getD i 0 ^ 2 ≤ his.getD (i + 1) 0

instance (q : ℚ) (N : ℕ) (los his : List ℚ) (m : ℕ) : Decidable (ChainOK q N los his m) := by
  unfold ChainOK; infer_instance

theorem exp_chain (q : ℚ) (N : ℕ) (los his : List ℚ) : ∀ m, ChainOK q N los his m →
    ((los.getD m 0 : ℚ) : ℝ) ≤ exp (2 ^ m * q) ∧ exp (2 ^ m * q) ≤ ((his.getD m 0 : ℚ) : ℝ)
  | 0, ⟨hq, hN, hlo, hhi, _⟩ => by
    have h := RatExpLog.abs_exp_sub_le q hq N hN
    have hlo' : ((los.getD 0 0 : ℚ) : ℝ) ≤ ((RatExpLog.expSum q N - RatExpLog.expRem N : ℚ) : ℝ) := by
      qc hlo
    have hhi' : ((RatExpLog.expSum q N + RatExpLog.expRem N : ℚ) : ℝ) ≤ ((his.getD 0 0 : ℚ) : ℝ) := by
      qc hhi
    push_cast at hlo' hhi'
    simp only [pow_zero, one_mul]
    constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]
  | m + 1, hc => by
    obtain ⟨hq, hN, hlo, hhi, hs⟩ := hc
    have ih := exp_chain q N los his m ⟨hq, hN, hlo, hhi, fun i hi => hs i (by omega)⟩
    obtain ⟨h0, hl, hh⟩ := hs m (by omega)
    have e : exp (2 ^ (m + 1) * (q : ℝ)) = exp (2 ^ m * q) ^ 2 := by
      rw [pow_succ, sq, ← exp_add]; congr 1; ring
    rw [e]
    have h0' : (0 : ℝ) ≤ los.getD m 0 := by qc h0
    have hl' : ((los.getD (m + 1) 0 : ℚ) : ℝ) ≤ ((los.getD m 0 : ℚ) : ℝ) ^ 2 := by qc hl
    have hh' : ((his.getD m 0 : ℚ) : ℝ) ^ 2 ≤ ((his.getD (m + 1) 0 : ℚ) : ℝ) := by qc hh
    constructor
    · exact hl'.trans (pow_le_pow_left₀ h0' ih.1 2)
    · exact (pow_le_pow_left₀ (exp_pos _).le ih.2 2).trans hh'

/-- `erfc x` between rational bounds from a model of `erfcxN` and an enclosure of `exp (-x²)`. -/
theorem erfc_model_encl (x : ℚ) (hx : 0 < x) (p : List ℚ) (a b c s eD : ℚ)
    (hmodel : ∀ y ∈ Icc (a : ℝ) b, |erfcxN y - eval p (y - c)| ≤ (s : ℝ) + eD * ((b : ℝ) - y))
    (hab : a ≤ x ∧ x ≤ b) (Elo Ehi : ℚ) (hE : (Elo : ℝ) ≤ exp (-(x : ℝ) ^ 2) ∧
      exp (-(x : ℝ) ^ 2) ≤ Ehi) (hElo : 0 ≤ Elo)
    (hPD : 0 ≤ evalQ p (x - c) - (s + eD * (b - x))) :
    ((Elo * sLo * (evalQ p (x - c) - (s + eD * (b - x))) : ℚ) : ℝ) ≤ erfc x ∧
      erfc x ≤ ((Ehi * sHi * (evalQ p (x - c) + (s + eD * (b - x))) : ℚ) : ℝ) := by
  have hm := hmodel x ⟨by qc hab.1, by qc hab.2⟩
  have hpv : eval p ((x : ℝ) - c) = (evalQ p (x - c) : ℝ) := by
    rw [PolyCalc.evalQ_cast]; push_cast; ring_nf
  rw [hpv] at hm
  have hPD' : (0 : ℝ) ≤ (evalQ p (x - c) : ℝ) - (s + eD * (b - x)) := by
    have : ((evalQ p (x - c) - (s + eD * (b - x)) : ℚ) : ℝ) ≥ 0 := by qc hPD
    push_cast at this; linarith
  have hN1 : (evalQ p (x - c) : ℝ) - (s + eD * (b - x)) ≤ erfcxN x := by
    linarith [(abs_le.mp hm).1]
  have hN2 : erfcxN x ≤ (evalQ p (x - c) : ℝ) + (s + eD * (b - x)) := by
    linarith [(abs_le.mp hm).2]
  have hs1 := scale_lo
  have hs2 := scale_hi
  have hsl0 : (0 : ℝ) ≤ sLo := by
    have : (0 : ℚ) ≤ sLo := by decide +kernel
    qc this
  have hErfc : erfc x = exp (-(x : ℝ) ^ 2) * (scale * erfcxN x) := by
    rw [erfc_eq, erfcx_eq]
  have hElo' : (0 : ℝ) ≤ Elo := by qc hElo
  rw [hErfc]
  push_cast
  constructor
  · have k1 : (sLo : ℝ) * ((evalQ p (x - c) : ℝ) - (s + eD * (b - x))) ≤ scale * erfcxN x :=
      mul_le_mul hs1 hN1 hPD' (scale_pos.le)
    have k2 := mul_le_mul hE.1 k1 (mul_nonneg hsl0 hPD') (exp_pos _).le
    linarith
  · have hN0 : 0 ≤ erfcxN x := (erfcxN_pos x).le
    have k1 : scale * erfcxN x ≤ (sHi : ℝ) * ((evalQ p (x - c) : ℝ) + (s + eD * (b - x))) :=
      mul_le_mul hs2 hN2 hN0 (by linarith [scale_pos])
    have k2 := mul_le_mul hE.2 k1 (mul_nonneg scale_pos.le hN0) (by linarith)
    linarith

/-- One step for a fixed nonnegative word `w` from a rational enclosure of `y` in the interior of
the binade of exponent field `e`. -/
theorem hard_within (y : ℝ) (w : UInt64) (hw : w.toNat < limit) (Ylo Yhi : ℚ)
    (hy : (Ylo : ℝ) ≤ y ∧ y ≤ Yhi) (e : ℕ) (he : 1 ≤ e) (he' : e ≤ 2046)
    (hb : ((2 : ℚ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 ≤ Ylo) (hyt : Yhi < 2 ^ 1023)
    (hd1 : ratOfWord w - Ylo < 2 ^ (e - 1) / 2 ^ 1074)
    (hd2 : Yhi - ratOfWord w < 2 ^ (e - 1) / 2 ^ 1074) :
    F64SignedRounding.WithinSteps 1 y w := by
  have hv : value w = (ratOfWord w : ℝ) := (ratOfWord_cast w).symm
  have hb' : (((2 : ℚ) ^ (e + 51) + 2 * 2 ^ (e - 1)) / 2 ^ 1074 : ℚ) ≤ (Ylo : ℝ) := by
    qc hb
  push_cast at hb'
  have hyt' : y < F64PositiveRounding.overflowThreshold :=
    F64NearestSteps.below_threshold y (by
      have : (Yhi : ℝ) < 2 ^ 1023 := by qc hyt
      linarith [hy.2])
  have hd1' : ((ratOfWord w - Ylo : ℚ) : ℝ) < ((2 ^ (e - 1) / 2 ^ 1074 : ℚ) : ℝ) := by
    qc hd1
  have hd2' : ((Yhi - ratOfWord w : ℚ) : ℝ) < ((2 ^ (e - 1) / 2 ^ 1074 : ℚ) : ℝ) := by
    qc hd2
  push_cast at hd1' hd2'
  refine F64NearestSteps.within_of_interior y (value w) w e he he' (by linarith [hy.1]) hyt'
    ⟨hw, fun v _ => by rw [sub_self, abs_zero]; exact abs_nonneg _⟩ ?_
  rw [hv, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

/-- One step for a fixed nonnegative word `w` from a rational enclosure of `y` within half a
spacing of `w`, for `y` at or above the start of the binade of exponent field `e`. -/
theorem half_within (y : ℝ) (w : UInt64) (hw : w.toNat < limit) (Ylo Yhi : ℚ)
    (hy : (Ylo : ℝ) ≤ y ∧ y ≤ Yhi) (e : ℕ) (he : 1 ≤ e) (he' : e ≤ 2046)
    (hb : (2 : ℚ) ^ (e + 51) / 2 ^ 1074 ≤ Ylo) (hyt : Yhi < 2 ^ 1023)
    (hd1 : ratOfWord w - Ylo < 2 ^ (e - 1) / 2 ^ 1074 / 2)
    (hd2 : Yhi - ratOfWord w < 2 ^ (e - 1) / 2 ^ 1074 / 2) :
    F64SignedRounding.WithinSteps 1 y w := by
  have hv : value w = (ratOfWord w : ℝ) := (ratOfWord_cast w).symm
  have hb' : (((2 : ℚ) ^ (e + 51) / 2 ^ 1074 : ℚ) : ℝ) ≤ (Ylo : ℝ) := by qc hb
  push_cast at hb'
  have hyt' : y < F64PositiveRounding.overflowThreshold :=
    F64NearestSteps.below_threshold y (by
      have : (Yhi : ℝ) < 2 ^ 1023 := by qc hyt
      linarith [hy.2])
  have hd1' : ((ratOfWord w - Ylo : ℚ) : ℝ) < ((2 ^ (e - 1) / 2 ^ 1074 / 2 : ℚ) : ℝ) := by
    qc hd1
  have hd2' : ((Yhi - ratOfWord w : ℚ) : ℝ) < ((2 ^ (e - 1) / 2 ^ 1074 / 2 : ℚ) : ℝ) := by
    qc hd2
  push_cast at hd1' hd2'
  refine F64NearestSteps.within_of_half y (value w) w e he he' (by linarith [hy.1]) hyt'
    ⟨hw, fun v _ => by rw [sub_self, abs_zero]; exact abs_nonneg _⟩ ?_
  rw [hv, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

#print axioms hardCase_cases
#print axioms erf_encl
#print axioms exp_chain
#print axioms erfc_model_encl
#print axioms hard_within
#print axioms half_within

end Verified.Examples.ErfcHardBase
