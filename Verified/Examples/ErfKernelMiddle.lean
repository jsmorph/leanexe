import LeanExe.ProofKit.RealErf
import LeanExe.ProofKit.PolyCalculus
import Verified.Examples.ErfKernelSmall

/-!
The approximation error of `s_erf.c`'s rational function on `0.84375 ≤ |x| < 1.25`, where
`erf |x|` is `erx + P (s)/Q (s)` with `s = |x| - 1`, `P` and `Q` of degree 6, and `erx` the single
precision value `0x3FEB0AC160000000`, as `Erf.erfMiddle` holds the coefficients.  The target is
`erf (1 + s) - erx`, with `erf (1 + s)` from the partial sum of 26 terms of the series at 0,
shifted to `s` with `PolyBound.shift`.  The check compares `Q ((2/√π)_lo T (s) - erx) - P` with
`(5/4) 2^-58 Q` on `[-5/32, 1/4]`.  The largest error, about `2^-58.20`, is at `s = 1/4`, where the
source states `2^-59.06`.
-/

namespace Verified.Examples.ErfKernelMiddle
open LeanExe.ProofKit PolyBound PolyChecks PolyCalculus RealErf ErfKernelSmall

/-- `pa0 + pa1 s + ... + pa6 s⁶`. -/
def erfPA : List ℚ :=
  [ratOfWord 0xBF6359B8BEF77538, ratOfWord 0x3FDA8D00AD92B34D, ratOfWord 0xBFD7D240FBB8C3F1,
    ratOfWord 0x3FD45FCA805120E4, ratOfWord 0xBFBC63983D3E28EC, ratOfWord 0x3FA22A36599795EB,
    ratOfWord 0xBF61BF380A96073F]

/-- `1 + qa1 s + ... + qa6 s⁶`. -/
def erfQA : List ℚ :=
  [1, ratOfWord 0x3FBB3E6618EEE323, ratOfWord 0x3FE14AF092EB6F33, ratOfWord 0x3FB2635CD99FE9A7,
    ratOfWord 0x3FC02660E763351F, ratOfWord 0x3F8BEDC26B51DD1C, ratOfWord 0x3F888B545735151D]

/-- `erx`, `0x3FEB0AC160000000`. -/
def erx : ℚ := ratOfWord 0x3FEB0AC160000000

/-- `(1 + s) E ((1 + s)²)`, the partial sum of `∫₀^(1+s) exp (-t²) dt` in `s`. -/
def middleT : List ℚ := shift 1 (oddP (erfCoeffs 26))

/-- `Q (κ_lo T - erx) - P`. -/
def middleA : List ℚ := subP (mulP erfQA (subP (scaleP kappaLo middleT) [erx])) erfPA

def middleEps : ℚ := (5 / 4) / 2 ^ 58

def middleM : ℚ := middleEps * (11 / 10)

def middleUp : List ℚ := addP (subP middleA (scaleP middleEps erfQA)) [middleM]

def middleLo : List ℚ := subP (addP middleA (scaleP middleEps erfQA)) [middleM]

theorem middle_up_1 : check middleUp (-5 / 32 : ℚ) (-27 / 256 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_up_2 : check middleUp (-27 / 256 : ℚ) (-7 / 128 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_up_3 : check middleUp (-7 / 128 : ℚ) (-1 / 256 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_up_4 : check middleUp (-1 / 256 : ℚ) (3 / 64 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_up_5 : check middleUp (3 / 64 : ℚ) (25 / 256 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_up_6 : check middleUp (25 / 256 : ℚ) (19 / 128 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_up_7 : check middleUp (19 / 128 : ℚ) (51 / 256 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_up_8 : check middleUp (51 / 256 : ℚ) (1 / 4 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_lo_1 : check middleLo (-5 / 32 : ℚ) (-27 / 256 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_lo_2 : check middleLo (-27 / 256 : ℚ) (-7 / 128 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_lo_3 : check middleLo (-7 / 128 : ℚ) (-1 / 256 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_lo_4 : check middleLo (-1 / 256 : ℚ) (3 / 64 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_lo_5 : check middleLo (3 / 64 : ℚ) (25 / 256 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_lo_6 : check middleLo (25 / 256 : ℚ) (19 / 128 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_lo_7 : check middleLo (19 / 128 : ℚ) (51 / 256 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_lo_8 : check middleLo (51 / 256 : ℚ) (1 / 4 : ℚ) middleM 20 = true := by
  decide +kernel

theorem middle_up_covers : Covers middleUp middleM 20 (-5 / 32 : ℚ) (1 / 4 : ℚ)
    [(-27 / 256 : ℚ), (-7 / 128 : ℚ), (-1 / 256 : ℚ), (3 / 64 : ℚ), (25 / 256 : ℚ), (19 / 128 : ℚ), (51 / 256 : ℚ)] :=
  ⟨middle_up_1, middle_up_2, middle_up_3, middle_up_4, middle_up_5, middle_up_6, middle_up_7, middle_up_8⟩

theorem middle_lo_covers : Covers middleLo middleM 20 (-5 / 32 : ℚ) (1 / 4 : ℚ)
    [(-27 / 256 : ℚ), (-7 / 128 : ℚ), (-1 / 256 : ℚ), (3 / 64 : ℚ), (25 / 256 : ℚ), (19 / 128 : ℚ), (51 / 256 : ℚ)] :=
  ⟨middle_lo_1, middle_lo_2, middle_lo_3, middle_lo_4, middle_lo_5, middle_lo_6, middle_lo_7, middle_lo_8⟩

theorem qa_check : check (subP erfQA [1]) (-5 / 32) (1 / 4) (1 / 10) 18 = true := by
  decide +kernel

theorem series_check : check (subP (erfCoeffs 26) [73 / 100]) (729 / 1024) (25 / 16) (1 / 10) 18 =
    true := by
  decide +kernel

theorem qa_pos (s : ℝ) (hs0 : -5 / 32 ≤ s) (hs1 : s ≤ 1 / 4) : 9 / 10 ≤ eval erfQA s := by
  have h := check_sound _ _ _ _ _ qa_check s (by push_cast; linarith) (by push_cast; linarith)
  rw [eval_subP] at h
  simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
  have := (abs_le.mp h).1
  push_cast at this
  linarith

theorem eval_middleT (s : ℝ) : eval middleT s = (1 + s) * eval (erfCoeffs 26) ((1 + s) ^ 2) := by
  rw [middleT, eval_shift, eval_oddP, Rat.cast_one]

/-- `|erf (1 + s) - erx - P (s)/Q (s)| ≤ (21/16) 2^-58` for `-5/32 ≤ s ≤ 1/4`. -/
theorem middle_kernel_error (s : ℝ) (hs0 : -5 / 32 ≤ s) (hs1 : s ≤ 1 / 4) :
    |erf (1 + s) - erx - eval erfPA s / eval erfQA s| ≤ (21 / 16) / 2 ^ 58 := by
  have hq := qa_pos s hs0 hs1
  have hw := abs_le_weighted middleA erfQA middleEps (-5 / 32) (1 / 4) middleM middleM
    (bounded_of_covers _ _ _ _ _ _ middle_up_covers)
    (bounded_of_covers _ _ _ _ _ _ middle_lo_covers) s (by push_cast; linarith)
    (by push_cast; linarith)
  have he : eval middleA s =
      ((kappaLo : ℝ) * eval middleT s - erx) * eval erfQA s - eval erfPA s := by
    simp only [middleA, eval_subP, eval_mulP, eval_scaleP, eval_cons, eval_nil, mul_zero,
      add_zero]
    ring
  rw [he] at hw
  have hp := sub_div_le _ _ _ _ (by linarith) hw
  set x := 1 + s with hx
  have hx0 : 27 / 32 ≤ x := by linarith
  have hx1 : x ≤ 5 / 4 := by linarith
  have hz0 : (729 / 1024 : ℝ) ≤ x ^ 2 := by nlinarith
  have hz1 : x ^ 2 ≤ 25 / 16 := by nlinarith
  have hE : |eval (erfCoeffs 26) (x ^ 2)| ≤ 1 := by
    have h := check_sound _ _ _ _ _ series_check (x ^ 2) (by push_cast; linarith)
      (by push_cast; linarith)
    rw [eval_subP] at h
    simp only [eval_cons, eval_nil, mul_zero, add_zero] at h
    have h1 := abs_le.mp h
    push_cast at h1
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2]
  rw [eval_middleT] at hp
  have hk := kappa_near
  have hser := erf_series 26 x
  have hsc := scale_bounds
  have hax : |x| = x := abs_of_pos (by linarith)
  have hrem : scale * (|x| ^ (2 * 26 + 1) / ((Nat.factorial 26 * (2 * 26 + 1) : ℕ) : ℝ)) ≤
      1 / 2 ^ 70 := by
    rw [hax]
    have hf : ((Nat.factorial 26 * (2 * 26 + 1) : ℕ) : ℝ) = 21374447439710098685952000000 := by
      norm_num [Nat.factorial]
    rw [hf]
    have h2 : scale ≤ 2 := by linarith [hsc.2]
    have hxp : x ^ (2 * 26 + 1) ≤ (5 / 4) ^ (2 * 26 + 1) :=
      pow_le_pow_left₀ (by linarith) hx1 _
    calc scale * (x ^ (2 * 26 + 1) / 21374447439710098685952000000) ≤ 2 * ((5 / 4) ^ (2 * 26 + 1) / 21374447439710098685952000000) := by
          gcongr
      _ ≤ 1 / 2 ^ 70 := by norm_num
  have hsplit : erf x - erx - eval erfPA s / eval erfQA s =
      (erf x - scale * (x * eval (erfCoeffs 26) (x ^ 2))) +
        (scale - kappaLo) * (x * eval (erfCoeffs 26) (x ^ 2)) +
        ((kappaLo : ℝ) * (x * eval (erfCoeffs 26) (x ^ 2)) - erx -
          eval erfPA s / eval erfQA s) := by ring
  rw [hsplit]
  have h2 : |(scale - kappaLo) * (x * eval (erfCoeffs 26) (x ^ 2))| ≤ 3 / 2 ^ 68 * (5 / 4) := by
    rw [abs_mul, abs_mul, hax]
    apply mul_le_mul hk _ (by positivity) (by norm_num)
    calc x * |eval (erfCoeffs 26) (x ^ 2)| ≤ (5 / 4) * 1 :=
          mul_le_mul hx1 hE (abs_nonneg _) (by norm_num)
      _ = 5 / 4 := by norm_num
  have hsum := abs_add_three (erf x - scale * (x * eval (erfCoeffs 26) (x ^ 2)))
    ((scale - kappaLo) * (x * eval (erfCoeffs 26) (x ^ 2)))
    ((kappaLo : ℝ) * (x * eval (erfCoeffs 26) (x ^ 2)) - erx - eval erfPA s / eval erfQA s)
  have heps : (middleEps : ℝ) = (5 / 4) / 2 ^ 58 := by simp [middleEps]
  rw [heps] at hp
  have hfin : (1 : ℝ) / 2 ^ 70 + 3 / 2 ^ 68 * (5 / 4) + (5 / 4) / 2 ^ 58 ≤ (21 / 16) / 2 ^ 58 := by
    norm_num
  have hp' := hp
  linarith [hser.trans hrem]

#print axioms middle_kernel_error

end Verified.Examples.ErfKernelMiddle
