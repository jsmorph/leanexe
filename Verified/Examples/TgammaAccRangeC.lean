import LeanExe.ProofKit.GammaScaled
import Verified.Examples.TgammaFactsBase

/-!
Relative bounds on the polynomials of `Tgamma.accurate` above `1/4` (`tgamma.c` lines 347-612,
commit `ff2f71f6`) for the ranges with `j = 16, 8, 4`.  For `floor x` in a range, the code evaluates
`poly3` at `d = 2 (x - (floor x + 1/2))` and multiplies by `2 ^ eoff` and a product of shifts; the
polynomial approximates `Γ (j + (1 + d)/2) / 2 ^ eoff` for `|d| ≤ 1`.  `accList oh imax ol jmax`
holds the `imax` doubles at `oh` plus the `jmax` double-doubles at `ol` of `Tgamma.accurateTable`,
the offsets of `Tgamma.accurateRange`.  Each range is covered by four pieces of radius `1/4` in `d`
and degree 20 for `j = 16` and eight pieces of radius `1/8` in `d` and degree 18 for `j = 8, 4`,
each checked by `GammaScaled.gammaScaledOk` against `Γ / 2 ^ k` for a power `k` that keeps the
scaled value near 1, with the bound `2 ^ -62` relative.
-/

namespace Verified.Examples.TgammaAccRangeC

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

/-- The parameters: radius `1/16` in `x`, degree 18, 100 bits, at most 40 terms, and Mathlib's
20-digit bounds on `π`. -/
def cfgR8 : Cfg := ⟨1 / 16, 18, 100, 40, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfgR8_pi : ((cfgR8.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfgR8.piHi : ℚ) : ℝ) := pi_bounds20

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

theorem r16_0 : gammaScaledOk cfgR ⟨(129 / 8), 0, log2Lo, log2Hi,
    ⟨4,
      (39460140009725338086696816199 / 5070602400912917605986812821504),
      (157840560038901352346787264799 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 41 log2Lo log2Hi
    (scaleP (2) (dilate 2 (PolyBound.shift (-3 / 4) (accList 522 11 533 29)))) εin εout
    (316063873 / 536870912) 2 = true := by
  decide +kernel

theorem r16_1 : gammaScaledOk cfgR ⟨(131 / 8), 0, log2Lo, log2Hi,
    ⟨4,
      (469883785660160440906038844505 / 20282409603651670423947251286016),
      (117470946415040110226509711127 / 5070602400912917605986812821504)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 42 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (-1 / 4) (accList 522 11 533 29)))) εin εout
    (628415985 / 1073741824) 2 = true := by
  decide +kernel

theorem r16_2 : gammaScaledOk cfgR ⟨(133 / 8), 0, log2Lo, log2Hi,
    ⟨4,
      (777198901322680523450135614811 / 20282409603651670423947251286016),
      (388599450661340261725067807407 / 10141204801825835211973625643008)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 43 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (1 / 4) (accList 522 11 533 29)))) εin εout
    (627209285 / 1073741824) 2 = true := by
  decide +kernel

theorem r16_3 : gammaScaledOk cfgR ⟨(135 / 8), 0, log2Lo, log2Hi,
    ⟨4,
      (539963526309064522751208978045 / 10141204801825835211973625643008),
      (1079927052618129045502417956093 / 20282409603651670423947251286016)⟩,
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩⟩ 44 log2Lo log2Hi
    (scaleP (1 / 4) (dilate 2 (PolyBound.shift (3 / 4) (accList 522 11 533 29)))) εin εout
    (314227159 / 536870912) 2 = true := by
  decide +kernel

/-- The range `j = 16`: `|Γ (j + (1 + d)/2) - 2 ^ 42 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range16 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((16 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (42 : ℕ) * eval (accList 522 11 533 29) d| ≤
      1 / 2 ^ 62 * Gamma (((16 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 4) (by norm_num) (lo := -1) (r := 1 / 4) (by norm_num)
    (fun d => |Gamma (((16 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (42 : ℕ) * eval (accList 522 11 533 29) d| ≤
      1 / 2 ^ 62 * Gamma (((16 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      522 11 533 29 16 42 41 (-3 / 4) (2) _ _ _ (by norm_num) (by norm_num) r16_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      522 11 533 29 16 42 42 (-1 / 4) (1) _ _ _ (by norm_num) (by norm_num) r16_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      522 11 533 29 16 42 43 (1 / 4) (1 / 2) _ _ _ (by norm_num) (by norm_num) r16_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR cfgR_pi (1 / 4) (by norm_num [cfgR])
      522 11 533 29 16 42 44 (3 / 4) (1 / 4) _ _ _ (by norm_num) (by norm_num) r16_3 s hs
    convert hb using 4 <;> norm_num

theorem r8_0 : gammaScaledOk cfgR8 ⟨(129 / 16), 8, log2Lo, log2Hi,
    ⟨4,
      (79073821807712628507644966105 / 20282409603651670423947251286016),
      (19768455451928157126911241527 / 5070602400912917605986812821504)⟩,
    ⟨28,
      (226984244944046465377247783957 / 20282409603651670423947251286016),
      (28373030618005808172155972995 / 2535301200456458802993406410752)⟩⟩ 12 log2Lo log2Hi
    (scaleP (4) (dilate 2 (PolyBound.shift (-7 / 8) (accList 591 10 601 28)))) εin εout
    (653996851 / 536870912) 1 = true := by
  decide +kernel

theorem r8_1 : gammaScaledOk cfgR8 ⟨(131 / 16), 8, log2Lo, log2Hi,
    ⟨4,
      (236302590590896026213265836807 / 20282409603651670423947251286016),
      (118151295295448013106632918405 / 10141204801825835211973625643008)⟩,
    ⟨28,
      (2044552802153817403158318071449 / 20282409603651670423947251286016),
      (511138200538454350789579517863 / 5070602400912917605986812821504)⟩⟩ 13 log2Lo log2Hi
    (scaleP (2) (dilate 2 (PolyBound.shift (-5 / 8) (accList 591 10 601 28)))) εin εout
    (842262851 / 1073741824) 1 = true := by
  decide +kernel

theorem r8_2 : gammaScaledOk cfgR8 ⟨(133 / 16), 8, log2Lo, log2Hi,
    ⟨4,
      (24520118458287268002627174227 / 1267650600228229401496703205376),
      (392321895332596288042034787635 / 20282409603651670423947251286016)⟩,
    ⟨28,
      (3841147924149639756915063068987 / 20282409603651670423947251286016),
      (1920573962074819878457531534495 / 10141204801825835211973625643008)⟩⟩ 13 log2Lo log2Hi
    (scaleP (2) (dilate 2 (PolyBound.shift (-3 / 8) (accList 591 10 601 28)))) εin εout
    (271736741 / 268435456) 1 = true := by
  decide +kernel

theorem r8_3 : gammaScaledOk cfgR8 ⟨(135 / 16), 8, log2Lo, log2Hi,
    ⟨4,
      (273575100701882645664555789073 / 10141204801825835211973625643008),
      (547150201403765291329111578149 / 20282409603651670423947251286016)⟩,
    ⟨28,
      (5617267025580780574010219344889 / 20282409603651670423947251286016),
      (1404316756395195143502554836223 / 5070602400912917605986812821504)⟩⟩ 14 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (-1 / 8) (accList 591 10 601 28)))) εin εout
    (351385223 / 536870912) 1 = true := by
  decide +kernel

theorem r8_4 : gammaScaledOk cfgR8 ⟨(137 / 16), 8, log2Lo, log2Hi,
    ⟨4,
      (350402777249855875209961874077 / 10141204801825835211973625643008),
      (700805554499711750419923748157 / 20282409603651670423947251286016)⟩,
    ⟨28,
      (921673676180804536341681698903 / 2535301200456458802993406410752),
      (7373389409446436290733453591227 / 20282409603651670423947251286016)⟩⟩ 14 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (1 / 8) (accList 591 10 601 28)))) εin εout
    (910561327 / 1073741824) 1 = true := by
  decide +kernel

theorem r8_5 : gammaScaledOk cfgR8 ⟨(139 / 16), 8, log2Lo, log2Hi,
    ⟨4,
      (106663199157778369728635808885 / 2535301200456458802993406410752),
      (853305593262226957829086471083 / 20282409603651670423947251286016)⟩,
    ⟨29,
      (-4948717869026914696166834859421 / 20282409603651670423947251286016),
      (-2474358934513457348083417429709 / 10141204801825835211973625643008)⟩⟩ 14 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (3 / 8) (accList 591 10 601 28)))) εin εout
    (1182094181 / 1073741824) 1 = true := by
  decide +kernel

theorem r8_6 : gammaScaledOk cfgR8 ⟨(141 / 16), 8, log2Lo, log2Hi,
    ⟨4,
      (502333780715361158963212079627 / 10141204801825835211973625643008),
      (1004667561430722317926424159257 / 20282409603651670423947251286016)⟩,
    ⟨29,
      (-3231219035945409419472903799227 / 20282409603651670423947251286016),
      (-403902379493176177434112974903 / 2535301200456458802993406410752)⟩⟩ 15 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (5 / 8) (accList 591 10 601 28)))) εin εout
    (768774781 / 1073741824) 1 = true := by
  decide +kernel

theorem r8_7 : gammaScaledOk cfgR8 ⟨(143 / 16), 8, log2Lo, log2Hi,
    ⟨4,
      (1154908319543312167760318508029 / 20282409603651670423947251286016),
      (1127840155804015788828436043 / 19807040628566084398385987584)⟩,
    ⟨29,
      (-1532379001487759226020245102155 / 20282409603651670423947251286016),
      (-191547375185969903252530637769 / 2535301200456458802993406410752)⟩⟩ 15 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (7 / 8) (accList 591 10 601 28)))) εin εout
    (1001838527 / 1073741824) 1 = true := by
  decide +kernel

/-- The range `j = 8`: `|Γ (j + (1 + d)/2) - 2 ^ 14 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range8 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((8 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (14 : ℕ) * eval (accList 591 10 601 28) d| ≤
      1 / 2 ^ 62 * Gamma (((8 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 8) (by norm_num) (lo := -1) (r := 1 / 8) (by norm_num)
    (fun d => |Gamma (((8 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (14 : ℕ) * eval (accList 591 10 601 28) d| ≤
      1 / 2 ^ 62 * Gamma (((8 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      591 10 601 28 8 14 12 (-7 / 8) (4) _ _ _ (by norm_num) (by norm_num) r8_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      591 10 601 28 8 14 13 (-5 / 8) (2) _ _ _ (by norm_num) (by norm_num) r8_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      591 10 601 28 8 14 13 (-3 / 8) (2) _ _ _ (by norm_num) (by norm_num) r8_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      591 10 601 28 8 14 14 (-1 / 8) (1) _ _ _ (by norm_num) (by norm_num) r8_3 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      591 10 601 28 8 14 14 (1 / 8) (1) _ _ _ (by norm_num) (by norm_num) r8_4 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      591 10 601 28 8 14 14 (3 / 8) (1) _ _ _ (by norm_num) (by norm_num) r8_5 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      591 10 601 28 8 14 15 (5 / 8) (1 / 2) _ _ _ (by norm_num) (by norm_num) r8_6 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      591 10 601 28 8 14 15 (7 / 8) (1 / 2) _ _ _ (by norm_num) (by norm_num) r8_7 s hs
    convert hb using 4 <;> norm_num

theorem r4_0 : gammaScaledOk cfgR8 ⟨(65 / 16), 12, log2Lo, log2Hi,
    ⟨4,
      (79073821807712628507644966105 / 20282409603651670423947251286016),
      (19768455451928157126911241527 / 5070602400912917605986812821504)⟩,
    ⟨38,
      (-2833458411572271186018508837535 / 20282409603651670423947251286016),
      (-708364602893067796504627209383 / 5070602400912917605986812821504)⟩⟩ 3 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (-7 / 8) (accList 657 9 666 26)))) εin εout
    (99656663 / 134217728) 0 = true := by
  decide +kernel

theorem r4_1 : gammaScaledOk cfgR8 ⟨(67 / 16), 12, log2Lo, log2Hi,
    ⟨4,
      (236302590590896026213265836807 / 20282409603651670423947251286016),
      (118151295295448013106632918405 / 10141204801825835211973625643008)⟩,
    ⟨38,
      (431637534450789876130479846363 / 10141204801825835211973625643008),
      (863275068901579752260959692729 / 20282409603651670423947251286016)⟩⟩ 3 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (-5 / 8) (accList 657 9 666 26)))) εin εout
    (29213853 / 33554432) 0 = true := by
  decide +kernel

theorem r4_2 : gammaScaledOk cfgR8 ⟨(69 / 16), 12, log2Lo, log2Hi,
    ⟨4,
      (24520118458287268002627174227 / 1267650600228229401496703205376),
      (392321895332596288042034787635 / 20282409603651670423947251286016)⟩,
    ⟨38,
      (1123689770830801338373056699715 / 5070602400912917605986812821504),
      (4494759083323205353492226798863 / 20282409603651670423947251286016)⟩⟩ 3 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (-3 / 8) (accList 657 9 666 26)))) εin εout
    (550442625 / 536870912) 0 = true := by
  decide +kernel

theorem r4_3 : gammaScaledOk cfgR8 ⟨(71 / 16), 12, log2Lo, log2Hi,
    ⟨4,
      (273575100701882645664555789073 / 10141204801825835211973625643008),
      (547150201403765291329111578149 / 20282409603651670423947251286016)⟩,
    ⟨38,
      (8063605165655183690678052141537 / 20282409603651670423947251286016),
      (2015901291413795922669513035385 / 5070602400912917605986812821504)⟩⟩ 3 log2Lo log2Hi
    (scaleP (1) (dilate 2 (PolyBound.shift (-1 / 8) (accList 657 9 666 26)))) εin εout
    (162725163 / 134217728) 0 = true := by
  decide +kernel

theorem r4_4 : gammaScaledOk cfgR8 ⟨(73 / 16), 12, log2Lo, log2Hi,
    ⟨4,
      (350402777249855875209961874077 / 10141204801825835211973625643008),
      (700805554499711750419923748157 / 20282409603651670423947251286016)⟩,
    ⟨39,
      (-621610235300980168962152824905 / 5070602400912917605986812821504),
      (-2486440941203920675848611299617 / 20282409603651670423947251286016)⟩⟩ 4 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (1 / 8) (accList 657 9 666 26)))) εin εout
    (386393079 / 536870912) 0 = true := by
  decide +kernel

theorem r4_5 : gammaScaledOk cfgR8 ⟨(75 / 16), 12, log2Lo, log2Hi,
    ⟨4,
      (106663199157778369728635808885 / 2535301200456458802993406410752),
      (853305593262226957829086471083 / 20282409603651670423947251286016)⟩,
    ⟨39,
      (120537058939023020189418646393 / 2535301200456458802993406410752),
      (964296471512184161515349171147 / 20282409603651670423947251286016)⟩⟩ 4 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (3 / 8) (accList 657 9 666 26)))) εin εout
    (921068737 / 1073741824) 0 = true := by
  decide +kernel

theorem r4_6 : gammaScaledOk cfgR8 ⟨(77 / 16), 12, log2Lo, log2Hi,
    ⟨4,
      (502333780715361158963212079627 / 10141204801825835211973625643008),
      (1004667561430722317926424159257 / 20282409603651670423947251286016)⟩,
    ⟨39,
      (2179633344265041816220466725203 / 10141204801825835211973625643008),
      (4359266688530083632440933450409 / 20282409603651670423947251286016)⟩⟩ 4 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (5 / 8) (accList 657 9 666 26)))) εin εout
    (137743833 / 134217728) 1 = true := by
  decide +kernel

theorem r4_7 : gammaScaledOk cfgR8 ⟨(79 / 16), 12, log2Lo, log2Hi,
    ⟨4,
      (1154908319543312167760318508029 / 20282409603651670423947251286016),
      (1127840155804015788828436043 / 19807040628566084398385987584)⟩,
    ⟨39,
      (962560615885976924615740572945 / 2535301200456458802993406410752),
      (7700484927087815396925924583563 / 20282409603651670423947251286016)⟩⟩ 4 log2Lo log2Hi
    (scaleP (1 / 2) (dilate 2 (PolyBound.shift (7 / 8) (accList 657 9 666 26)))) εin εout
    (1323189133 / 1073741824) 1 = true := by
  decide +kernel

/-- The range `j = 4`: `|Γ (j + (1 + d)/2) - 2 ^ 3 P (d)| ≤ 2 ^ -62 Γ` for `|d| ≤ 1`. -/
theorem range4 : ∀ d : ℝ, |d| ≤ 1 →
    |Gamma (((4 : ℕ) : ℝ) + (1 + d) / 2) - 2 ^ (3 : ℕ) * eval (accList 657 9 666 26) d| ≤
      1 / 2 ^ 62 * Gamma (((4 : ℕ) : ℝ) + (1 + d) / 2) := by
  intro d hd
  have hd' := abs_le.mp hd
  refine cover_pieces (K := 8) (by norm_num) (lo := -1) (r := 1 / 8) (by norm_num)
    (fun d => |Gamma (((4 : ℕ) : ℝ) + (1 + d) / 2) -
        2 ^ (3 : ℕ) * eval (accList 657 9 666 26) d| ≤
      1 / 2 ^ 62 * Gamma (((4 : ℕ) : ℝ) + (1 + d) / 2)) ?_ d (by linarith) (by norm_num; linarith)
  intro i hi s hs
  interval_cases i
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      657 9 666 26 4 3 3 (-7 / 8) (1) _ _ _ (by norm_num) (by norm_num) r4_0 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      657 9 666 26 4 3 3 (-5 / 8) (1) _ _ _ (by norm_num) (by norm_num) r4_1 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      657 9 666 26 4 3 3 (-3 / 8) (1) _ _ _ (by norm_num) (by norm_num) r4_2 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      657 9 666 26 4 3 3 (-1 / 8) (1) _ _ _ (by norm_num) (by norm_num) r4_3 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      657 9 666 26 4 3 4 (1 / 8) (1 / 2) _ _ _ (by norm_num) (by norm_num) r4_4 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      657 9 666 26 4 3 4 (3 / 8) (1 / 2) _ _ _ (by norm_num) (by norm_num) r4_5 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      657 9 666 26 4 3 4 (5 / 8) (1 / 2) _ _ _ (by norm_num) (by norm_num) r4_6 s hs
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfgR8 cfgR8_pi (1 / 8) (by norm_num [cfgR8])
      657 9 666 26 4 3 4 (7 / 8) (1 / 2) _ _ _ (by norm_num) (by norm_num) r4_7 s hs
    convert hb using 4 <;> norm_num

#print axioms range16
#print axioms range8
#print axioms range4

end Verified.Examples.TgammaAccRangeC
