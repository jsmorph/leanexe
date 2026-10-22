import Library.Numerics.Float64.Tgamma.TgammaFactsBase

/-!
A bound on CORE-MATH's polynomial for `Γ` about 3.5 (`tgamma.c` lines 812-855, commit `ff2f71f6`).
For `x` in `(-3, 4]` outside the other cases, `cr_tgamma` evaluates the polynomial at
`d = x - (i + 3.5)` with `i = roundeven (x - 3.5)` and `|d| ≤ 1/2`, and divides by the product of
the shifts.  `mainList` holds the double-double coefficients `cc [0]` to `cc [9]` and the doubles
`c [10]` to `c [17]` of `Tgamma.mainTable`; `polyddd` adds `d · (c [10] + ⋯)` to the coefficient of
degree 9.  `gamma_main` bounds `|Γ (7/2 + d) - P (d)|` by `2 ^ -62` for `|d| ≤ 1/2`, where `Γ ≥ 2`
(`gamma_main_ge`).  The proof covers `[-1/2, 1/2]` by eight pieces of radius `1/16` with thirteen
shifts each.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaPolyMain

open Real LeanExe.ProofKit PolyBound TaylorModel GammaBasic GammaModels GammaFits GammaThresholds
  TgammaFactsBase

/-- The Taylor-model parameters: radius `1 / 16`, degree 18, 100 bits, at most 60 series terms with
remainder factor below `2 ^ -80`, and Mathlib's 20-digit bounds on `π`. -/
def cfg : Cfg := ⟨1 / 16, 18, 100, 60, 1 / 2 ^ 80, piLo20, piHi20⟩

theorem cfg_pi : ((cfg.piLo : ℚ) : ℝ) ≤ π ∧ π ≤ ((cfg.piHi : ℚ) : ℝ) := pi_bounds20

theorem main_piece0 : gammaPieceOk cfg ⟨(49 / 16), 13, log2Lo, log2Hi,
    ⟨4,
      (79073821807712628507644966105 / 20282409603651670423947251286016),
      (19768455451928157126911241527 / 5070602400912917605986812821504)⟩,
    ⟨39,
      (5808559819847643023401628865433 / 20282409603651670423947251286016),
      (1452139954961910755850407216359 / 5070602400912917605986812821504)⟩⟩
    (PolyBound.shift (-7 / 16) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem main_piece1 : gammaPieceOk cfg ⟨(51 / 16), 13, log2Lo, log2Hi,
    ⟨4,
      (236302590590896026213265836807 / 20282409603651670423947251286016),
      (118151295295448013106632918405 / 10141204801825835211973625643008)⟩,
    ⟨40,
      (-3741997148445428755619741023191 / 20282409603651670423947251286016),
      (-935499287111357188904935255797 / 5070602400912917605986812821504)⟩⟩
    (PolyBound.shift (-5 / 16) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem main_piece2 : gammaPieceOk cfg ⟨(53 / 16), 13, log2Lo, log2Hi,
    ⟨4,
      (24520118458287268002627174227 / 1267650600228229401496703205376),
      (392321895332596288042034787635 / 20282409603651670423947251286016)⟩,
    ⟨40,
      (83709466206831228814442011273 / 2535301200456458802993406410752),
      (669675729654649830515536090187 / 20282409603651670423947251286016)⟩⟩
    (PolyBound.shift (-3 / 16) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem main_piece3 : gammaPieceOk cfg ⟨(55 / 16), 13, log2Lo, log2Hi,
    ⟨4,
      (273575100701882645664555789073 / 10141204801825835211973625643008),
      (547150201403765291329111578149 / 20282409603651670423947251286016)⟩,
    ⟨40,
      (2494904028223805543572861561447 / 10141204801825835211973625643008),
      (4989808056447611087145723122897 / 20282409603651670423947251286016)⟩⟩
    (PolyBound.shift (-1 / 16) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem main_piece4 : gammaPieceOk cfg ⟨(57 / 16), 13, log2Lo, log2Hi,
    ⟨4,
      (350402777249855875209961874077 / 10141204801825835211973625643008),
      (700805554499711750419923748157 / 20282409603651670423947251286016)⟩,
    ⟨41,
      (-4835789268819057803424573935077 / 20282409603651670423947251286016),
      (-2417894634409528901712286967537 / 10141204801825835211973625643008)⟩⟩
    (PolyBound.shift (1 / 16) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem main_piece5 : gammaPieceOk cfg ⟨(59 / 16), 13, log2Lo, log2Hi,
    ⟨4,
      (106663199157778369728635808885 / 2535301200456458802993406410752),
      (853305593262226957829086471083 / 20282409603651670423947251286016)⟩,
    ⟨41,
      (-171397276840961584827063640401 / 5070602400912917605986812821504),
      (-685589107363846339308254561601 / 20282409603651670423947251286016)⟩⟩
    (PolyBound.shift (3 / 16) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem main_piece6 : gammaPieceOk cfg ⟨(61 / 16), 13, log2Lo, log2Hi,
    ⟨4,
      (502333780715361158963212079627 / 10141204801825835211973625643008),
      (1004667561430722317926424159257 / 20282409603651670423947251286016)⟩,
    ⟨41,
      (3385524040240825206930226749955 / 20282409603651670423947251286016),
      (1692762020120412603465113374979 / 10141204801825835211973625643008)⟩⟩
    (PolyBound.shift (5 / 16) mainList) (1 / 2 ^ 62) 0 = true := by
  decide +kernel

theorem main_piece7 : gammaPieceOk cfg ⟨(63 / 16), 13, log2Lo, log2Hi,
    ⟨4,
      (1154908319543312167760318508029 / 20282409603651670423947251286016),
      (1127840155804015788828436043 / 19807040628566084398385987584)⟩,
    ⟨41,
      (7381070300475494820057826333089 / 20282409603651670423947251286016),
      (1845267575118873705014456583273 / 5070602400912917605986812821504)⟩⟩
    (PolyBound.shift (7 / 16) mainList) (1 / 2 ^ 62) 1 = true := by
  decide +kernel

theorem main_cover : ∀ x : ℝ, ((-1 : ℝ) / 2) ≤ x → x ≤ ((-1 : ℝ) / 2) + 2 * ((1 : ℝ) / 16) * 8 →
    |Gamma (((7 : ℝ) / 2) + x) - eval mainList x| ≤ 1 / 2 ^ 62 := by
  refine cover_pieces (K := 8) (by norm_num) (lo := ((-1 : ℝ) / 2)) (r := ((1 : ℝ) / 16))
    (by norm_num) (fun x => |Gamma (((7 : ℝ) / 2) + x) - eval mainList x| ≤ 1 / 2 ^ 62) ?_
  intro j hj t ht
  interval_cases j
  · have hb := piece_bound cfg cfg_pi _ mainList _ _ (7 / 2) (-7 / 16) (by norm_num)
      main_piece0 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ mainList _ _ (7 / 2) (-5 / 16) (by norm_num)
      main_piece1 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ mainList _ _ (7 / 2) (-3 / 16) (by norm_num)
      main_piece2 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ mainList _ _ (7 / 2) (-1 / 16) (by norm_num)
      main_piece3 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ mainList _ _ (7 / 2) (1 / 16) (by norm_num)
      main_piece4 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ mainList _ _ (7 / 2) (3 / 16) (by norm_num)
      main_piece5 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ mainList _ _ (7 / 2) (5 / 16) (by norm_num)
      main_piece6 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num
  · have hb := piece_bound cfg cfg_pi _ mainList _ _ (7 / 2) (7 / 16) (by norm_num)
      main_piece7 t (by simp only [cfg]; push_cast; exact ht)
    convert hb using 4 <;> norm_num

/-- CORE-MATH's polynomial about 3.5 is within `2 ^ -62` of `Γ (7/2 + d)` for `|d| ≤ 1/2`. -/
theorem gamma_main : ∀ d : ℝ, |d| ≤ 1 / 2 →
    |Real.Gamma (7 / 2 + d) - eval mainList d| ≤ 1 / 2 ^ 62 := by
  intro d hd
  have hd' := abs_le.mp hd
  exact main_cover d (by linarith) (by linarith)

theorem gamma_main_ge {d : ℝ} (hd : |d| ≤ 1 / 2) : 2 ≤ Gamma (7 / 2 + d) := by
  have hd' := abs_le.mp hd
  have h3 : Gamma 3 = 2 := by
    rw [show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Gamma_nat_eq_factorial]
    norm_num
  have h := Gamma_strictMonoOn_Ici.monotoneOn (a := 3) (b := 7 / 2 + d)
    (by norm_num [Set.mem_Ici]) (by rw [Set.mem_Ici]; linarith) (by linarith)
  rw [h3] at h
  exact h

#print axioms gamma_main
#print axioms gamma_main_ge

end Library.Numerics.Float64.Tgamma.TgammaPolyMain
