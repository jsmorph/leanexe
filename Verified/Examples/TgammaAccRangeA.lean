import LeanExe.ProofKit.GammaScaled
import Verified.Examples.TgammaFactsBase

/-!
Relative bounds on the polynomials of `Tgamma.accurate` above `1/4` (`tgamma.c` lines 347-612,
commit `ff2f71f6`) for the ranges with `j = 160, 128, 96`.  For `floor x` in a range, the code
evaluates `poly3` at `d = 2 (x - (floor x + 1/2))` and multiplies by `2 ^ eoff` and a product of
shifts; the polynomial approximates `Γ (j + (1 + d)/2) / 2 ^ eoff` for `|d| ≤ 1`.
`accList oh imax ol jmax` holds the `imax` doubles at `oh` plus the `jmax` double-doubles at `ol` of
`Tgamma.accurateTable`, the offsets of `Tgamma.accurateRange`.  Each range is covered by four pieces
of radius `1/4` in `d` and degree 20 for `j = 160, 128, 96`, each checked by
`GammaScaled.gammaScaledOk` against `Γ / 2 ^ k` for a power `k` that keeps the scaled value near 1,
with the bound `2 ^ -62` relative.
-/

namespace Verified.Examples.TgammaAccRangeA

set_option exponentiation.threshold 2048

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaRel
  GammaScaled GammaThresholds TgammaFactsBase

/-- The polynomial of one range of `Tgamma.accurate`. -/
def accList (oh imax ol jmax : ℕ) : List ℚ :=
  addP (coeffs Tgamma.accurateTable oh 1 imax) (ddCoeffs Tgamma.accurateTable ol jmax)

/-- The parameters: radius `1/8` in `x`, degree 20, 100 bits, at most 40 terms, and Mathlib's
20-digit bounds on `π`. -/
def cfgR : Cfg := ⟨1 / 8, 20, 100, 40, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfgR_pi : ((cfgR.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgR.piHi : ℚ) : ℝ) := pi_bounds20

/-- The relative bounds of the checks. -/
def εin : ℚ := 15 / 16 / 2 ^ 62

def εout : ℚ := 1 / 2 ^ 62

/-- One piece of radius `ρ` in `d`, checked with the parameters `cf` of radius `ρ/2` in `x`. -/
theorem piece_bound (cf : Cfg) (hpi : ((cf.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cf.piHi : ℚ) : ℝ)) (ρ : ℝ)
    (hr : ((cf.r : ℚ) : ℝ) = ρ / 2) (oh imax ol jmax j eoff k : ℕ) (d0 c : ℚ) (d : LgData) (m0 : ℚ)
    (depth : ℕ) (hd : d.a = j + (1 + d0) / 2) (hc : (c : ℝ) * 2 ^ k = 2 ^ eoff)
    (h : gammaScaledOk cf d k log2Lo log2Hi
      (scaleP c (dilate 2 (PolyBound.shift d0 (accList oh imax ol jmax)))) εin εout m0 depth = true)
    (s : ℝ) (hs : |s| ≤ ρ) :
    |Gamma (j + (1 + (d0 + s)) / 2) - 2 ^ eoff * eval (accList oh imax ol jmax) (d0 + s)| ≤
      1 / 2 ^ 62 * Gamma (j + (1 + (d0 + s)) / 2) := by
  have ht : |s / 2| ≤ ((cf.r : ℚ) : ℝ) := by
    rw [hr, abs_div, abs_two]
    linarith
  have hb := gammaScaledOk_sound cf d k log2Lo log2Hi _ εin εout m0 depth hpi h ht
  rw [eval_scaleP, eval_dilate, eval_shift] at hb
  have hx : ((d.a : ℚ) : ℝ) + s / 2 = j + (1 + (d0 + s)) / 2 := by
    rw [hd]
    push_cast
    ring
  have hy : ((d0 : ℚ) : ℝ) + ((2 : ℚ) : ℝ) * (s / 2) = d0 + s := by
    rw [show ((2 : ℚ) : ℝ) = 2 by norm_num]
    ring
  rw [hx, hy] at hb
  simp only [εout] at hb
  push_cast at hb
  have hk : (0 : ℝ) < 2 ^ k := by positivity
  have key : Gamma (j + (1 + (d0 + s)) / 2) - 2 ^ eoff * eval (accList oh imax ol jmax) (d0 + s) =
      2 ^ k * (Gamma (j + (1 + (d0 + s)) / 2) / 2 ^ k -
        c * eval (accList oh imax ol jmax) (d0 + s)) := by
    rw [← hc]
    field_simp
  rw [key, abs_mul, abs_of_pos hk]
  calc 2 ^ k * |Gamma (j + (1 + (d0 + s)) / 2) / 2 ^ k -
        c * eval (accList oh imax ol jmax) (d0 + s)|
      ≤ 2 ^ k * (1 / 2 ^ 62 * (Gamma (j + (1 + (d0 + s)) / 2) / 2 ^ k)) :=
        mul_le_mul_of_nonneg_left hb hk.le
    _ = 1 / 2 ^ 62 * Gamma (j + (1 + (d0 + s)) / 2) := by
        field_simp

theorem r160_0 : gammaScaledOk cfgR ⟨(1281 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (567716044274104766610416594031 / 2535301200456458802993406410752),
      (4541728354192838132883332752251 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 939 log2Lo log2Hi
    (scaleP (8) (dilate 2 (PolyBound.shift (-3 / 4) (accList 64 14 78 34)))) εin εout
    (674070613 / 1073741824) 3 = true := by
  decide +kernel

theorem r160_1 : gammaScaledOk cfgR ⟨(1283 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (2286685092632499348308008221581 / 10141204801825835211973625643008),
      (4573370185264998696616016443165 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 941 log2Lo log2Hi
    (scaleP (2) (dilate 2 (PolyBound.shift (-1 / 4) (accList 64 14 78 34)))) εin εout
    (598991689 / 1073741824) 3 = true := by
  decide +kernel

theorem r160_2 : gammaScaledOk cfgR ⟨(1285 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (575620341246997487738032427867 / 2535301200456458802993406410752),
      (4604962729975979901904259422939 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 943 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (1 / 4) (accList 64 14 78 34)))) εin εout
    (532483445 / 1073741824) 3 = true := by
  decide +kernel

theorem r160_3 : gammaScaledOk cfgR ⟨(1287 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (4636506141627153530411067335519 / 20282409603651670423947251286016),
      (2318253070813576765205533667761 / 10141204801825835211973625643008)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 945 log2Lo log2Hi
    (scaleP (1 / 8) (dilate 2 (PolyBound.shift (3 / 4) (accList 64 14 78 34)))) εin εout
    (236772399 / 536870912) 3 = true := by
  decide +kernel

/-- The range `j = 160`: `|Γ (j + (1 + d)/2) - 2 ^ 942 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range160 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((160 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (942 : ℕ) * eval (accList 64 14 78 34) d| ≤
      1 / 2 ^ 62 * Gamma (((160 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 4) (by norm_num) (lo := -1) (r := 1 / 4) (by norm_num)
    (fun d => |Gamma (((160 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (942 : ℕ) * eval (accList 64 14 78 34) d| ≤
      1 / 2 ^ 62 * Gamma (((160 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      64 14 78 34 160 942 939 (-3 / 4) (8) _ _ _ (by norm_num) (by norm_num) r160_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      64 14 78 34 160 942 941 (-1 / 4) (2) _ _ _ (by norm_num) (by norm_num) r160_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      64 14 78 34 160 942 943 (1 / 4) (1 / 2) _ _ _ (by norm_num) (by norm_num) r160_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      64 14 78 34 160 942 945 (3 / 4) (1 / 8) _ _ _ (by norm_num) (by norm_num) r160_3 s hs
    convert hb using 4 <;> norm_num

theorem r128_0 : gammaScaledOk cfgR ⟨(1025 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (19797375513889725122877629219 / 20282409603651670423947251286016),
      (9898687756944862561438814611 / 10141204801825835211973625643008)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 710 log2Lo log2Hi
    (scaleP (8) (dilate 2 (PolyBound.shift (-3 / 4) (accList 146 14 160 33)))) εin εout
    (37159365 / 67108864) 3 = true := by
  decide +kernel

theorem r128_1 : gammaScaledOk cfgR ⟨(1027 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (7416781107400772922487891073 / 2535301200456458802993406410752),
      (59334248859206183379903128587 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 712 log2Lo log2Hi
    (scaleP (2) (dilate 2 (PolyBound.shift (-1 / 4) (accList 146 14 160 33)))) εin εout
    (124897137 / 268435456) 3 = true := by
  decide +kernel

theorem r128_2 : gammaScaledOk cfgR ⟨(1029 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (98794202168897589921960546895 / 20282409603651670423947251286016),
      (49397101084448794960980273449 / 10141204801825835211973625643008)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 714 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (1 / 4) (accList 146 14 160 33)))) εin εout
    (104999967 / 268435456) 3 = true := by
  decide +kernel

theorem r128_3 : gammaScaledOk cfgR ⟨(1031 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (69088767080915508052015317535 / 10141204801825835211973625643008),
      (138177534161831016104030635073 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 715 log2Lo log2Hi
    (scaleP (1 / 4) (dilate 2 (PolyBound.shift (3 / 4) (accList 146 14 160 33)))) εin εout
    (353262787 / 536870912) 3 = true := by
  decide +kernel

/-- The range `j = 128`: `|Γ (j + (1 + d)/2) - 2 ^ 713 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range128 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((128 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (713 : ℕ) * eval (accList 146 14 160 33) d| ≤
      1 / 2 ^ 62 * Gamma (((128 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 4) (by norm_num) (lo := -1) (r := 1 / 4) (by norm_num)
    (fun d => |Gamma (((128 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (713 : ℕ) * eval (accList 146 14 160 33) d| ≤
      1 / 2 ^ 62 * Gamma (((128 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      146 14 160 33 128 713 710 (-3 / 4) (8) _ _ _ (by norm_num) (by norm_num) r128_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      146 14 160 33 128 713 712 (-1 / 4) (2) _ _ _ (by norm_num) (by norm_num) r128_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      146 14 160 33 128 713 714 (1 / 4) (1 / 2) _ _ _ (by norm_num) (by norm_num) r128_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      146 14 160 33 128 713 715 (3 / 4) (1 / 4) _ _ _ (by norm_num) (by norm_num) r128_3 s hs
    convert hb using 4 <;> norm_num

theorem r96_0 : gammaScaledOk cfgR ⟨(769 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (-1452123355072717254475552521365 / 5070602400912917605986812821504),
      (-5808493420290869017902210085457 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 493 log2Lo log2Hi
    (scaleP (4) (dilate 2 (PolyBound.shift (-3 / 4) (accList 226 13 239 32)))) εin εout
    (429384753 / 1073741824) 3 = true := by
  decide +kernel

theorem r96_1 : gammaScaledOk cfgR ⟨(771 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (-2877905903643352253377246368533 / 10141204801825835211973625643008),
      (-5755811807286704506754492737063 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 494 log2Lo log2Hi
    (scaleP (2) (dilate 2 (PolyBound.shift (-1 / 4) (accList 226 13 239 32)))) εin εout
    (83920867 / 134217728) 3 = true := by
  decide +kernel

theorem r96_2 : gammaScaledOk cfgR ⟨(773 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (-5703266675298110832665148047687 / 20282409603651670423947251286016),
      (-1425816668824527708166287011921 / 5070602400912917605986812821504)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 496 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (1 / 4) (accList 226 13 239 32)))) εin εout
    (262601237 / 536870912) 3 = true := by
  decide +kernel

theorem r96_3 : gammaScaledOk cfgR ⟨(775 / 8), 0, log2Lo, log2Hi,
    ⟨7,
      (-5650857318995661733890717038195 / 20282409603651670423947251286016),
      (-353178582437228858368169814887 / 1267650600228229401496703205376)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 497 log2Lo log2Hi
    (scaleP (1 / 4) (dilate 2 (PolyBound.shift (3 / 4) (accList 226 13 239 32)))) εin εout
    (411127303 / 536870912) 3 = true := by
  decide +kernel

/-- The range `j = 96`: `|Γ (j + (1 + d)/2) - 2 ^ 495 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range96 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((96 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (495 : ℕ) * eval (accList 226 13 239 32) d| ≤
      1 / 2 ^ 62 * Gamma (((96 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 4) (by norm_num) (lo := -1) (r := 1 / 4) (by norm_num)
    (fun d => |Gamma (((96 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (495 : ℕ) * eval (accList 226 13 239 32) d| ≤
      1 / 2 ^ 62 * Gamma (((96 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      226 13 239 32 96 495 493 (-3 / 4) (4) _ _ _ (by norm_num) (by norm_num) r96_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      226 13 239 32 96 495 494 (-1 / 4) (2) _ _ _ (by norm_num) (by norm_num) r96_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      226 13 239 32 96 495 496 (1 / 4) (1 / 2) _ _ _ (by norm_num) (by norm_num) r96_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      226 13 239 32 96 495 497 (3 / 4) (1 / 4) _ _ _ (by norm_num) (by norm_num) r96_3 s hs
    convert hb using 4 <;> norm_num

#print axioms range160
#print axioms range128
#print axioms range96

end Verified.Examples.TgammaAccRangeA
