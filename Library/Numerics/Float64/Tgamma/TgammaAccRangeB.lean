import LeanExe.ProofKit.GammaScaled
import Library.Numerics.Float64.Tgamma.TgammaFactsBase

/-!
Relative bounds on the polynomials of `Tgamma.accurate` above `1/4` (`tgamma.c` lines 347-612,
commit `ff2f71f6`) for the ranges with `j = 64, 32, 26`.  For `floor x` in a range, the code
evaluates `poly3` at `d = 2 (x - (floor x + 1/2))` and multiplies by `2 ^ eoff` and a product of
shifts; the polynomial approximates `Γ (j + (1 + d)/2) / 2 ^ eoff` for `|d| ≤ 1`.
`accList oh imax ol jmax` holds the `imax` doubles at `oh` plus the `jmax` double-doubles at `ol` of
`Tgamma.accurateTable`, the offsets of `Tgamma.accurateRange`.  Each range is covered by four pieces
of radius `1/4` in `d` and degree 20 for `j = 64, 32, 26`, each checked by
`GammaScaled.gammaScaledOk` against `Γ / 2 ^ k` for a power `k` that keeps the scaled value near 1,
with the bound `2 ^ -62` relative.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaAccRangeB

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

theorem r64_0 : gammaScaledOk cfgR ⟨(513 / 8), 0, log2Lo, log2Hi,
    ⟨6,
      (39575445929141779791978566973 / 20282409603651670423947251286016),
      (618366342642840309249665109 / 316912650057057350374175801344)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 291 log2Lo log2Hi
    (scaleP (4) (dilate 2 (PolyBound.shift (-3 / 4) (accList 303 13 316 32)))) εin εout
    (529716193 / 1073741824) 3 = true := by
  decide +kernel

theorem r64_1 : gammaScaledOk cfgR ⟨(515 / 8), 0, log2Lo, log2Hi,
    ⟨6,
      (118495427228029359020726239463 / 20282409603651670423947251286016),
      (59247713614014679510363119733 / 10141204801825835211973625643008)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 292 log2Lo log2Hi
    (scaleP (2) (dilate 2 (PolyBound.shift (-1 / 4) (accList 303 13 316 32)))) εin εout
    (748033849 / 1073741824) 3 = true := by
  decide +kernel

theorem r64_2 : gammaScaledOk cfgR ⟨(517 / 8), 0, log2Lo, log2Hi,
    ⟨6,
      (197109516359133056505719256541 / 20282409603651670423947251286016),
      (6159672386222908015803726767 / 633825300114114700748351602688)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 294 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (1 / 4) (accList 303 13 316 32)))) εin εout
    (528682611 / 1073741824) 3 = true := by
  decide +kernel

theorem r64_3 : gammaScaledOk cfgR ⟨(519 / 8), 0, log2Lo, log2Hi,
    ⟨6,
      (68855018858243003264443971339 / 5070602400912917605986812821504),
      (275420075432972013057775885359 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 295 log2Lo log2Hi
    (scaleP (1 / 4) (dilate 2 (PolyBound.shift (3 / 4) (accList 303 13 316 32)))) εin εout
    (374018351 / 536870912) 3 = true := by
  decide +kernel

/-- The range `j = 64`: `|Γ (j + (1 + d)/2) - 2 ^ 293 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range64 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((64 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (293 : ℕ) * eval (accList 303 13 316 32) d| ≤
      1 / 2 ^ 62 * Gamma (((64 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 4) (by norm_num) (lo := -1) (r := 1 / 4) (by norm_num)
    (fun d => |Gamma (((64 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (293 : ℕ) * eval (accList 303 13 316 32) d| ≤
      1 / 2 ^ 62 * Gamma (((64 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      303 13 316 32 64 293 291 (-3 / 4) (4) _ _ _ (by norm_num) (by norm_num) r64_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      303 13 316 32 64 293 292 (-1 / 4) (2) _ _ _ (by norm_num) (by norm_num) r64_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      303 13 316 32 64 293 294 (1 / 4) (1 / 2) _ _ _ (by norm_num) (by norm_num) r64_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      303 13 316 32 64 293 295 (3 / 4) (1 / 4) _ _ _ (by norm_num) (by norm_num) r64_3 s hs
    convert hb using 4 <;> norm_num

theorem r32_0 : gammaScaledOk cfgR ⟨(257 / 8), 0, log2Lo, log2Hi,
    ⟨5,
      (79073821807712628507644966105 / 20282409603651670423947251286016),
      (19768455451928157126911241527 / 5070602400912917605986812821504)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 113 log2Lo log2Hi
    (scaleP (4) (dilate 2 (PolyBound.shift (-3 / 4) (accList 380 12 392 30)))) εin εout
    (841719373 / 1073741824) 3 = true := by
  decide +kernel

theorem r32_1 : gammaScaledOk cfgR ⟨(259 / 8), 0, log2Lo, log2Hi,
    ⟨5,
      (236302590590896026213265836807 / 20282409603651670423947251286016),
      (118151295295448013106632918405 / 10141204801825835211973625643008)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 115 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (-1 / 4) (accList 380 12 392 30)))) εin εout
    (3898605 / 8388608) 3 = true := by
  decide +kernel

theorem r32_2 : gammaScaledOk cfgR ⟨(261 / 8), 0, log2Lo, log2Hi,
    ⟨5,
      (24520118458287268002627174227 / 1267650600228229401496703205376),
      (392321895332596288042034787635 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 116 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (1 / 4) (accList 380 12 392 30)))) εin εout
    (296432581 / 536870912) 3 = true := by
  decide +kernel

theorem r32_3 : gammaScaledOk cfgR ⟨(263 / 8), 0, log2Lo, log2Hi,
    ⟨5,
      (273575100701882645664555789073 / 10141204801825835211973625643008),
      (547150201403765291329111578149 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 117 log2Lo log2Hi
    (scaleP (1 / 4) (dilate 2 (PolyBound.shift (3 / 4) (accList 380 12 392 30)))) εin εout
    (705733655 / 1073741824) 3 = true := by
  decide +kernel

/-- The range `j = 32`: `|Γ (j + (1 + d)/2) - 2 ^ 115 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range32 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((32 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (115 : ℕ) * eval (accList 380 12 392 30) d| ≤
      1 / 2 ^ 62 * Gamma (((32 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 4) (by norm_num) (lo := -1) (r := 1 / 4) (by norm_num)
    (fun d => |Gamma (((32 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (115 : ℕ) * eval (accList 380 12 392 30) d| ≤
      1 / 2 ^ 62 * Gamma (((32 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      380 12 392 30 32 115 113 (-3 / 4) (4) _ _ _ (by norm_num) (by norm_num) r32_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      380 12 392 30 32 115 115 (-1 / 4) (1) _ _ _ (by norm_num) (by norm_num) r32_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      380 12 392 30 32 115 116 (1 / 4) (1 / 2) _ _ _ (by norm_num) (by norm_num) r32_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      380 12 392 30 32 115 117 (3 / 4) (1 / 4) _ _ _ (by norm_num) (by norm_num) r32_3 s hs
    convert hb using 4 <;> norm_num

theorem r26_0 : gammaScaledOk cfgR ⟨(209 / 8), 0, log2Lo, log2Hi,
    ⟨5,
      (-4114148715896559869242768407761 / 20282409603651670423947251286016),
      (-2057074357948279934621384203879 / 10141204801825835211973625643008)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 84 log2Lo log2Hi
    (scaleP (4) (dilate 2 (PolyBound.shift (-3 / 4) (accList 452 12 464 29)))) εin εout
    (852434675 / 1073741824) 3 = true := by
  decide +kernel

theorem r26_1 : gammaScaledOk cfgR ⟨(211 / 8), 0, log2Lo, log2Hi,
    ⟨5,
      (-3920981450068630900486627288555 / 20282409603651670423947251286016),
      (-490122681258578862560828411069 / 2535301200456458802993406410752)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 85 log2Lo log2Hi
    (scaleP (2) (dilate 2 (PolyBound.shift (-1 / 4) (accList 452 12 464 29)))) εin εout
    (239741681 / 268435456) 3 = true := by
  decide +kernel

theorem r26_2 : gammaScaledOk cfgR ⟨(213 / 8), 0, log2Lo, log2Hi,
    ⟨5,
      (-1864818272048799335333993357157 / 10141204801825835211973625643008),
      (-3729636544097598670667986714311 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 87 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (1 / 4) (accList 452 12 464 29)))) εin εout
    (540716931 / 1073741824) 3 = true := by
  decide +kernel

theorem r26_3 : gammaScaledOk cfgR ⟨(215 / 8), 0, log2Lo, log2Hi,
    ⟨5,
      (-1770039967215763708443338591987 / 10141204801825835211973625643008),
      (-3540079934431527416886677183971 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 88 log2Lo log2Hi
    (scaleP (1 / 4) (dilate 2 (PolyBound.shift (3 / 4) (accList 452 12 464 29)))) εin εout
    (611237879 / 1073741824) 3 = true := by
  decide +kernel

/-- The range `j = 26`: `|Γ (j + (1 + d)/2) - 2 ^ 86 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range26 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((26 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (86 : ℕ) * eval (accList 452 12 464 29) d| ≤
      1 / 2 ^ 62 * Gamma (((26 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 4) (by norm_num) (lo := -1) (r := 1 / 4) (by norm_num)
    (fun d => |Gamma (((26 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (86 : ℕ) * eval (accList 452 12 464 29) d| ≤
      1 / 2 ^ 62 * Gamma (((26 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      452 12 464 29 26 86 84 (-3 / 4) (4) _ _ _ (by norm_num) (by norm_num) r26_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      452 12 464 29 26 86 85 (-1 / 4) (2) _ _ _ (by norm_num) (by norm_num) r26_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      452 12 464 29 26 86 87 (1 / 4) (1 / 2) _ _ _ (by norm_num) (by norm_num) r26_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      452 12 464 29 26 86 88 (3 / 4) (1 / 4) _ _ _ (by norm_num) (by norm_num) r26_3 s hs
    convert hb using 4 <;> norm_num

#print axioms range64
#print axioms range32
#print axioms range26

end Library.Numerics.Float64.Tgamma.TgammaAccRangeB
