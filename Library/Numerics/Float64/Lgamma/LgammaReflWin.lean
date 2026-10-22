import Library.Numerics.Float64.Lgamma.LgammaReflMid
import Library.Numerics.Float64.Lgamma.LgammaZeroBase

/-!
`FastSpec` for the reflection of `Lgamma.lgammaWith` from `x = -4` to `-2`, where `ln |Γ x|` has
the zeros -2.7477, -2.4570, -3.9553, and -3.1436.  `negPointOk` encloses `ln |Γ|` at the ends of
a window about each zero (`p_a` to `p_h`), where `|ln |Γ|| ≥ 1/32`.  `ln |Γ|` is convex between
the poles (`GammaConvex.convexOn_lgamma_neg`), so `|ln |Γ x|| ≥ 1/32` outside the windows, and
the relative form of `FastSpec` holds there (`LgammaReflMid.refl_rel` with `|fh| ≤ 2`).  In the
windows the absolute form holds (`LgammaReflMid.refl_abs`): `ln Γ (-x)` is at least 0.24 above
2.5 (`lgamma_five_halves`), 0.17 from 2.42 to 2.5 by convexity (`lgamma_chord`), and `ln 2` above
3, and `s = sin (π φ)/π` is at least `p - π² p³/6` for `p` at most the distance of `φ` from the
integers (`s_ge`).  `refl_four` puts the cases together.
-/

namespace Library.Numerics.Float64.Lgamma.LgammaReflWin
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma Library.Numerics.Float64.Tgamma.TgammaDD Library.Numerics.Float64.Tgamma.TgammaWords LgammaFastSmall
  LgammaPiecePoly TgammaFloor LgammaWalk LgammaReflCore LgammaReflTail LgammaReflMid
  TaylorModel GammaModels GammaReflect GammaThresholds LgammaZeroBase

set_option exponentiation.threshold 4096

theorem p_a : negPointOk cfgZ 2 (25 / 32)
    (531997187043 / 838592085262)
    ⟨1,
      (-4828450423012659386639763843279 / 20282409603651670423947251286016),
      (-1207112605753164846659940960819 / 5070602400912917605986812821504)⟩
    ⟨(121 / 32), 13, log2Lo, log2Hi,
      ⟨4,
          (966932835004679150009473456989 / 20282409603651670423947251286016),
          (30216651093896223437796045531 / 633825300114114700748351602688)⟩,
      ⟨41,
          (593740749750400383239004335655 / 5070602400912917605986812821504),
          (2374962999001601532956017342623 / 20282409603651670423947251286016)⟩⟩
    (1411263842050703253899 / 18889465931478580854784)
    (728032934391235805583 / 9444732965739290427392) 0 = true := by
  decide +kernel

theorem p_b : negPointOk cfgZ 2 (23 / 32)
    (473848193588 / 612990667237)
    ⟨0,
      (326372755543883896777406774709 / 1267650600228229401496703205376),
      (5221964088702142348438508395347 / 20282409603651670423947251286016)⟩
    ⟨(119 / 32), 13, log2Lo, log2Hi,
      ⟨4,
          (891252114347082482851949500081 / 20282409603651670423947251286016),
          (222813028586770620712987375021 / 5070602400912917605986812821504)⟩,
      ⟨41,
          (169730687165911223324377843549 / 10141204801825835211973625643008),
          (339461374331822446648755687101 / 20282409603651670423947251286016)⟩⟩
    (-917374787943239404667 / 18889465931478580854784)
    (-1778295742782279461353 / 37778931862957161709568) 0 = true := by
  decide +kernel

theorem p_c : negPointOk cfgZ 2 (1 / 2)
    (1)
    ⟨0,
      (-1 / 20282409603651670423947251286016),
      (1 / 20282409603651670423947251286016)⟩
    ⟨(7 / 2), 13, log2Lo, log2Hi,
      ⟨4,
          (312061692631428082850567715063 / 10141204801825835211973625643008),
          (624123385262856165701135430129 / 20282409603651670423947251286016)⟩,
      ⟨40,
          (7116969553918904186513537453655 / 20282409603651670423947251286016),
          (3558484776959452093256768726829 / 10141204801825835211973625643008)⟩⟩
    (-33719186929573240305 / 590295810358705651712)
    (-1045813551538763883921 / 18889465931478580854784) 0 = true := by
  decide +kernel

theorem p_d : negPointOk cfgZ 2 (27 / 64)
    (487798042976 / 502868378075)
    ⟨0,
      (154283159498393392433781711019 / 5070602400912917605986812821504),
      (617132637993573569735126844079 / 20282409603651670423947251286016)⟩
    ⟨(219 / 64), 13, log2Lo, log2Hi,
      ⟨4,
          (527861175124789523900058454483 / 20282409603651670423947251286016),
          (263930587562394761950029227243 / 10141204801825835211973625643008)⟩,
      ⟨40,
          (2227319947400864261935615686817 / 10141204801825835211973625643008),
          (4454639894801728523871231373637 / 20282409603651670423947251286016)⟩⟩
    (2207164230080849478271 / 37778931862957161709568)
    (1138616467898850921331 / 18889465931478580854784) 0 = true := by
  decide +kernel

theorem p_e : negPointOk cfgZ 3 (31 / 32)
    (35577437217 / 362971589432)
    ⟨3,
      (2466050691509494727746112358881 / 10141204801825835211973625643008),
      (4932101383018989455492224717765 / 20282409603651670423947251286016)⟩
    ⟨(159 / 32), 12, log2Lo, log2Hi,
      ⟨4,
          (1192295260274472757159619771651 / 20282409603651670423947251286016),
          (596147630137236378579809885827 / 10141204801825835211973625643008)⟩,
      ⟨40,
          (-5531079533122169184055078388355 / 20282409603651670423947251286016),
          (-43211558852516946750430299909 / 158456325028528675187087900672)⟩⟩
    (1563070123372555651205 / 4722366482869645213696)
    (3149787885020340939 / 9223372036854775808) 0 = true := by
  decide +kernel

theorem p_f : negPointOk cfgZ 3 (15 / 16)
    (56590589113 / 290073790069)
    ⟨2,
      (1257500657315572273776847244361 / 5070602400912917605986812821504),
      (5030002629262289095107388977447 / 20282409603651670423947251286016)⟩
    ⟨(79 / 16), 12, log2Lo, log2Hi,
      ⟨4,
          (1154908319543312167760318508029 / 20282409603651670423947251286016),
          (1127840155804015788828436043 / 19807040628566084398385987584)⟩,
      ⟨39,
          (962560615885976924615740572945 / 2535301200456458802993406410752),
          (7700484927087815396925924583563 / 20282409603651670423947251286016)⟩⟩
    (-1464424992651495170751 / 4722366482869645213696)
    (-1419365762108372242419 / 4722366482869645213696) 0 = true := by
  decide +kernel

theorem p_g : negPointOk cfgZ 3 (5 / 32)
    (365079868529 / 774464140306)
    ⟨1,
      (74674799902014691588777211559 / 1267650600228229401496703205376),
      (1194796798432235065420435384947 / 20282409603651670423947251286016)⟩
    ⟨(133 / 32), 12, log2Lo, log2Hi,
      ⟨4,
          (197109516359133056505719256541 / 20282409603651670423947251286016),
          (6159672386222908015803726767 / 633825300114114700748351602688)⟩,
      ⟨38,
          (-54685154693327502289579822031 / 20282409603651670423947251286016),
          (-13671288673331875572394955507 / 5070602400912917605986812821504)⟩⟩
    (-453992337379674319015 / 4722366482869645213696)
    (-880046684766753295321 / 9444732965739290427392) 0 = true := by
  decide +kernel

theorem p_h : negPointOk cfgZ 3 (1 / 8)
    (403984654808 / 1055662776701)
    ⟨1,
      (1355879073737943014226550647013 / 5070602400912917605986812821504),
      (5423516294951772056906202588055 / 20282409603651670423947251286016)⟩
    ⟨(33 / 8), 12, log2Lo, log2Hi,
      ⟨4,
          (39460140009725338086696816199 / 5070602400912917605986812821504),
          (157840560038901352346787264799 / 20282409603651670423947251286016)⟩,
      ⟨38,
          (-976765127188573014210645690369 / 20282409603651670423947251286016),
          (-488382563594286507105322845183 / 10141204801825835211973625643008)⟩⟩
    (1434655091576970370047 / 9444732965739290427392)
    (185024962207347369153 / 1180591620717411303424) 0 = true := by
  decide +kernel

theorem v_a : (1 / 32 : ℝ) ≤ GammaBasic.lgamma (-89 / 32) := by
  have h := (negPointOk_sound cfgZ 2 _ _ _ _ _ _ 0 cfgZ_pi p_a).1
  have e : (-89 / 32 : ℝ) = -((2 : ℕ) : ℝ) - (((25 / 32) : ℚ) : ℝ) := by norm_num
  rw [e]
  exact le_trans (by norm_num) h

theorem v_b : GammaBasic.lgamma (-87 / 32) ≤ -(1 / 32 : ℝ) := by
  have h := (negPointOk_sound cfgZ 2 _ _ _ _ _ _ 0 cfgZ_pi p_b).2
  have e : (-87 / 32 : ℝ) = -((2 : ℕ) : ℝ) - (((23 / 32) : ℚ) : ℝ) := by norm_num
  rw [e]
  exact le_trans h (by norm_num)

theorem v_c : GammaBasic.lgamma (-5 / 2) ≤ -(1 / 32 : ℝ) := by
  have h := (negPointOk_sound cfgZ 2 _ _ _ _ _ _ 0 cfgZ_pi p_c).2
  have e : (-5 / 2 : ℝ) = -((2 : ℕ) : ℝ) - (((1 / 2) : ℚ) : ℝ) := by norm_num
  rw [e]
  exact le_trans h (by norm_num)

theorem v_d : (1 / 32 : ℝ) ≤ GammaBasic.lgamma (-155 / 64) := by
  have h := (negPointOk_sound cfgZ 2 _ _ _ _ _ _ 0 cfgZ_pi p_d).1
  have e : (-155 / 64 : ℝ) = -((2 : ℕ) : ℝ) - (((27 / 64) : ℚ) : ℝ) := by norm_num
  rw [e]
  exact le_trans (by norm_num) h

theorem v_e : (1 / 32 : ℝ) ≤ GammaBasic.lgamma (-127 / 32) := by
  have h := (negPointOk_sound cfgZ 3 _ _ _ _ _ _ 0 cfgZ_pi p_e).1
  have e : (-127 / 32 : ℝ) = -((3 : ℕ) : ℝ) - (((31 / 32) : ℚ) : ℝ) := by norm_num
  rw [e]
  exact le_trans (by norm_num) h

theorem v_f : GammaBasic.lgamma (-63 / 16) ≤ -(1 / 32 : ℝ) := by
  have h := (negPointOk_sound cfgZ 3 _ _ _ _ _ _ 0 cfgZ_pi p_f).2
  have e : (-63 / 16 : ℝ) = -((3 : ℕ) : ℝ) - (((15 / 16) : ℚ) : ℝ) := by norm_num
  rw [e]
  exact le_trans h (by norm_num)

theorem v_g : GammaBasic.lgamma (-101 / 32) ≤ -(1 / 32 : ℝ) := by
  have h := (negPointOk_sound cfgZ 3 _ _ _ _ _ _ 0 cfgZ_pi p_g).2
  have e : (-101 / 32 : ℝ) = -((3 : ℕ) : ℝ) - (((5 / 32) : ℚ) : ℝ) := by norm_num
  rw [e]
  exact le_trans h (by norm_num)

theorem v_h : (1 / 32 : ℝ) ≤ GammaBasic.lgamma (-25 / 8) := by
  have h := (negPointOk_sound cfgZ 3 _ _ _ _ _ _ 0 cfgZ_pi p_h).1
  have e : (-25 / 8 : ℝ) = -((3 : ℕ) : ℝ) - (((1 / 8) : ℚ) : ℝ) := by norm_num
  rw [e]
  exact le_trans (by norm_num) h

/-- `s = sin (π φ)/π ≥ σ` when `0 < p ≤ φ'` and `σ ≤ p - 9.9225 p³/6`, from `sin y ≥ y - y³/6`
and `π² ≤ 9.9225`. -/
theorem s_ge (φ p σ : ℝ) (hp : 0 < p) (hpz : p ≤ 1 / 2 - |φ - 1 / 2|)
    (hσ : σ ≤ p - 99225 / 10 ^ 4 * p ^ 3 / 6) : σ ≤ Real.sin (Real.pi * φ) / Real.pi := by
  rw [le_div_iff₀ Real.pi_pos]
  have hc := s_cube φ p hp hpz
  have hpi := Real.pi_pos
  have hpi' := Real.pi_lt_d2
  have hpi2 : Real.pi ^ 2 ≤ 99225 / 10 ^ 4 := by nlinarith
  have hp3 : 0 ≤ p ^ 3 := by positivity
  have hcube : (Real.pi * p) ^ 3 / 6 ≤ Real.pi * (99225 / 10 ^ 4 * p ^ 3 / 6) := by
    rw [show (Real.pi * p) ^ 3 / 6 = Real.pi * (Real.pi ^ 2 * p ^ 3 / 6) by ring]
    apply mul_le_mul_of_nonneg_left _ hpi.le
    nlinarith
  have := mul_le_mul_of_nonneg_right hσ hpi.le
  linarith

theorem lgamma_three : GammaBasic.lgamma 3 = Real.log 2 := by
  rw [GammaBasic.lgamma, show (3 : ℝ) = (2 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]

theorem lgamma_four_le : GammaBasic.lgamma 4 ≤ 19 / 10 := by
  rw [GammaBasic.lgamma, show (4 : ℝ) = (3 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
  norm_num [Nat.factorial]
  rw [show (6 : ℝ) = 2 ^ 2 * (3 / 2) by norm_num, Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow]
  have := Real.log_two_lt_d9
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
  push_cast
  linarith

/-- `ln Γ (5/2) = ln (3 √π/4) ≥ 0.2477`, from `ln y ≥ 1 - 1/y`. -/
theorem lgamma_five_halves : (2477 / 10 ^ 4 : ℝ) ≤ GammaBasic.lgamma (5 / 2) := by
  have hG : Real.Gamma (5 / 2) = 3 / 4 * √Real.pi := by
    rw [show (5 / 2 : ℝ) = 3 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      show (3 / 2 : ℝ) = 1 / 2 + 1 by norm_num, Real.Gamma_add_one (by norm_num),
      Real.Gamma_one_half_eq]
    ring
  have hsq : (17724 / 10 ^ 4 : ℝ) ≤ √Real.pi := by
    have h := Real.sqrt_le_sqrt (show (17724 / 10 ^ 4 : ℝ) ^ 2 ≤ Real.pi by
      have := Real.pi_gt_d6; norm_num; linarith)
    rwa [Real.sqrt_sq (by norm_num)] at h
  have hy : (13293 / 10 ^ 4 : ℝ) ≤ 3 / 4 * √Real.pi := by linarith
  have hinv : (3 / 4 * √Real.pi)⁻¹ ≤ 10 ^ 4 / 13293 := by
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 13293 / 10 ^ 4) hy
    rwa [inv_div] at this
  have hl := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 3 / 4 * √Real.pi by linarith)
  rw [GammaBasic.lgamma, hG]
  linarith

/-- `ln Γ a ≥ 0.17` from 2.42 to 2.5, from the chord of the convex `ln Γ` from 2.5 to 3. -/
theorem lgamma_chord (a : ℝ) (h0 : 155 / 64 ≤ a) (h1 : a ≤ 5 / 2) :
    (17 / 100 : ℝ) ≤ GammaBasic.lgamma a := by
  have h25 := lgamma_five_halves
  have h25u : GammaBasic.lgamma (5 / 2) ≤ Real.log 2 := by
    rw [← lgamma_three]; exact lgamma_mono (by norm_num) (by norm_num)
  have hl2 := Real.log_two_lt_d9
  unfold GammaBasic.lgamma at h25 h25u ⊢
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]; linarith
  have hc := Real.convexOn_log_Gamma.slope_mono_adjacent (x := a) (y := 5 / 2) (z := 3)
    (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by norm_num)) h (by norm_num)
  simp only [Function.comp] at hc
  have h3 : Real.log (Real.Gamma 3) = Real.log 2 := lgamma_three
  rw [h3, div_le_div_iff₀ (by linarith) (by norm_num)] at hc
  have hD : (Real.log 2 - Real.log (Real.Gamma (5 / 2))) * (5 / 2 - a) ≤
      (Real.log 2 - Real.log (Real.Gamma (5 / 2))) * (5 / 64) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith

/-- `|fh| ≤ 2` for a piece at `a` from 2 to 4, where `0 ≤ ln Γ a ≤ 1.9`. -/
theorem fh_two (fh fl eps : Float) (a : ℝ) (ha2 : 2 ≤ a) (ha4 : a ≤ 4)
    (hfhb : |value fh.toBits| ≤ 16) (hflb : |value fl.toBits| ≤ 1 / 2 ^ 38)
    (hehi : value eps.toBits ≤ |value fh.toBits| / 2 ^ 63 + 1 / 2 ^ 78)
    (hpos : |GammaBasic.lgamma a - (value fh.toBits + value fl.toBits)| +
      |value fh.toBits| / 2 ^ 65 ≤ 2 * value eps.toBits) :
    |value fh.toBits| ≤ 2 := by
  have hl0 : 0 ≤ GammaBasic.lgamma a := by
    have := lgamma_mono (le_refl 2) ha2
    rwa [GammaBasic.lgamma_two] at this
  have hl4 : GammaBasic.lgamma a ≤ 19 / 10 := (lgamma_mono ha2 ha4).trans lgamma_four_le
  have h1 := abs_sub_abs_le_abs_sub (value fh.toBits + value fl.toBits) (GammaBasic.lgamma a)
  rw [abs_sub_comm, abs_of_nonneg hl0] at h1
  have h2 := abs_sub_abs_le_abs_sub (value fh.toBits) (-value fl.toBits)
  rw [sub_neg_eq_add, abs_neg] at h2
  have h3 : |value fh.toBits| / 2 ^ 63 ≤ 16 / 2 ^ 63 := div_le_div_of_nonneg_right hfhb (by norm_num)
  have : 0 ≤ |value fh.toBits| / 2 ^ 65 := by positivity
  linarith [(by norm_num : (19 : ℝ) / 10 + 1 / 2 ^ 38 + 2 * (16 / 2 ^ 63 + 1 / 2 ^ 78) ≤ 2)]

set_option maxHeartbeats 1000000 in
/-- **The reflection from -4 to -2**: the relative form of `FastSpec` outside the windows about
the zeros, where `|ln |Γ x|| ≥ 1/32`, and the absolute form in them. -/
theorem refl_four (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hL : LgammaApprox.LogFact)
    (hS : LgammaApprox.SinpiFact) (x : Float) (hx : Finite x.toBits)
    (h4 : -4 < value x.toBits) (h2 : value x.toBits < -2)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (fh fl eps : Float) (hfh : Finite fh.toBits)
    (hfl : Finite fl.toBits) (he : Finite eps.toBits) (hfhb : |value fh.toBits| ≤ 16)
    (hflb : |value fl.toBits| ≤ 1 / 2 ^ 38)
    (helo : |value fh.toBits| * (869 / 10 ^ 22) + 98 / 10 ^ 26 ≤ value eps.toBits)
    (hehi : value eps.toBits ≤ |value fh.toBits| / 2 ^ 63 + 1 / 2 ^ 78)
    (hpos : |GammaBasic.lgamma (-value x.toBits) - (value fh.toBits + value fl.toBits)| +
      |value fh.toBits| / 2 ^ 65 ≤ 2 * value eps.toBits)
    (A B C D : Float × Float)
    (hA : A = Lgamma.asSinpipid Lgamma.sinpiTable (x - floorF x))
    (hB : B = mulDDD (-x) A.1 A.2)
    (hC : C = Lgamma.asLogd Tgamma.logdTable B.1)
    (hD : D = sumDD fh fl C.1 (C.2 + B.2 / B.1)) (sign : Float) :
    FastSpec (Real.log (Real.Gamma (value x.toBits)))
      (-D.1, -D.2, eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
  have hrel : 1 / 32 ≤ |GammaBasic.lgamma (value x.toBits)| →
      FastSpec (Real.log (Real.Gamma (value x.toBits)))
        (-D.1, -D.2, eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
    intro hLb
    have hF2 := fh_two fh fl eps (-value x.toBits) (by linarith) (by linarith) hfhb hflb hehi hpos
    exact refl_rel hF hL hS x hx (by linarith) (by linarith) hint fh fl eps hfh hfl he 2 hF2
      (by norm_num) hflb helo hehi hpos (le_trans (by norm_num) hLb) A B C D hA hB hC hD sign
  have habs : ∀ lam σ p : ℝ, lam ≤ GammaBasic.lgamma (-value x.toBits) → 1 / 8 ≤ lam → 0 < σ →
      σ ≤ 1 → 0 < p → p ≤ 1 / 2 - |Int.fract (value x.toBits) - 1 / 2| →
      σ ≤ p - 99225 / 10 ^ 4 * p ^ 3 / 6 →
      114 / 100 / 2 ^ 71 / σ + 24 / 10 ^ 22 ≤ lam * (27 / 10 ^ 21) →
      FastSpec (Real.log (Real.Gamma (value x.toBits)))
        (-D.1, -D.2, eps + C.1.abs * Float.ofBits 0x3B8E392010175EE6, sign) := by
    intro lam σ p hlam hlam0 hσ0 hσ1 hp hpz hσp hbud
    exact refl_abs hF hL hS x hx (by linarith) (by linarith) hint fh fl eps hfh hfl he hfhb hflb
      helo hehi hpos lam σ hlam hlam0 hσ0 hσ1 (fun _ => s_ge _ p σ hp hpz hσp) hbud
      A B C D hA hB hC hD sign
  set v := value x.toBits with hvdef
  have hl2 := Real.log_two_gt_d9
  have hm3 : v ≠ -3 := by have := hint (-3); push_cast at this; exact this
  rcases lt_or_gt_of_ne hm3 with h3 | h3
  · -- from -4 to -3
    have hfr : Int.fract v = v + 4 := by
      rw [← Int.self_sub_floor, show ⌊v⌋ = -4 from
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩]
      push_cast; ring
    have hcv := GammaConvex.convexOn_lgamma_neg 3
    have mem : ∀ y : ℝ, -4 < y → y < -3 → y ∈ Set.Ioo (-((3 : ℕ) : ℝ) - 1) (-((3 : ℕ) : ℝ)) :=
      fun y h1 h2 => ⟨by push_cast; linarith, by push_cast; linarith⟩
    have hlam3 : (69 / 100 : ℝ) ≤ GammaBasic.lgamma (-v) := by
      have := lgamma_mono (show (2 : ℝ) ≤ 3 by norm_num) (show (3 : ℝ) ≤ -v by linarith)
      rw [lgamma_three] at this
      linarith
    have ve := v_e
    have vf := v_f
    have vg := v_g
    have vh := v_h
    by_cases hA1 : v ≤ -127 / 32
    · apply hrel
      have := GammaConvex.convex_left hcv (mem v h4 h3) (mem (-63 / 16) (by norm_num) (by norm_num))
        hA1 (by norm_num) (by linarith) (by linarith)
      rw [abs_of_pos (by linarith)]
      linarith
    by_cases hA2 : v < -63 / 16
    · refine habs (69 / 100) (31 / 1000) (1 / 32) hlam3 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) ?_ (by norm_num) (by norm_num)
      rw [hfr]
      have : |v + 4 - 1 / 2| ≤ 15 / 32 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    by_cases hA3 : v ≤ -101 / 32
    · apply hrel
      have := GammaConvex.convex_mid hcv (mem (-63 / 16) (by norm_num) (by norm_num))
        (mem (-101 / 32) (by norm_num) (by norm_num)) (by linarith) hA3
      have hm : max (GammaBasic.lgamma (-63 / 16)) (GammaBasic.lgamma (-101 / 32)) ≤ -1 / 32 :=
        max_le (by linarith) (by linarith)
      rw [abs_of_neg (by linarith)]
      linarith
    by_cases hA4 : v < -25 / 8
    · refine habs (69 / 100) (3 / 25) (1 / 8) hlam3 (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) ?_ (by norm_num) (by norm_num)
      rw [hfr]
      have : |v + 4 - 1 / 2| ≤ 3 / 8 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    · apply hrel
      have := GammaConvex.convex_right hcv (mem v h4 h3) (mem (-101 / 32) (by norm_num) (by norm_num))
        (by linarith : (-25 / 8 : ℝ) ≤ v) (by norm_num) (by linarith) (by linarith)
      rw [abs_of_pos (by linarith)]
      linarith
  · -- from -3 to -2
    have hfr : Int.fract v = v + 3 := by
      rw [← Int.self_sub_floor, show ⌊v⌋ = -3 from
        Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩]
      push_cast; ring
    have hcv := GammaConvex.convexOn_lgamma_neg 2
    have mem : ∀ y : ℝ, -3 < y → y < -2 → y ∈ Set.Ioo (-((2 : ℕ) : ℝ) - 1) (-((2 : ℕ) : ℝ)) :=
      fun y h1 h2 => ⟨by push_cast; linarith, by push_cast; linarith⟩
    have va := v_a
    have vb := v_b
    have vc := v_c
    have vd := v_d
    by_cases hA1 : v ≤ -89 / 32
    · apply hrel
      have := GammaConvex.convex_left hcv (mem v h3 h2) (mem (-87 / 32) (by norm_num) (by norm_num))
        hA1 (by norm_num) (by linarith) (by linarith)
      rw [abs_of_pos (by linarith)]
      linarith
    by_cases hA2 : v < -87 / 32
    · have hlam : (6 / 25 : ℝ) ≤ GammaBasic.lgamma (-v) := by
        have := lgamma_mono (show (2 : ℝ) ≤ 5 / 2 by norm_num) (show (5 / 2 : ℝ) ≤ -v by linarith)
        linarith [lgamma_five_halves]
      refine habs (6 / 25) (1 / 5) (7 / 32) hlam (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) ?_ (by norm_num) (by norm_num)
      rw [hfr]
      have : |v + 3 - 1 / 2| ≤ 9 / 32 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    by_cases hA3 : v ≤ -5 / 2
    · apply hrel
      have := GammaConvex.convex_mid hcv (mem (-87 / 32) (by norm_num) (by norm_num))
        (mem (-5 / 2) (by norm_num) (by norm_num)) (by linarith) hA3
      have hm : max (GammaBasic.lgamma (-87 / 32)) (GammaBasic.lgamma (-5 / 2)) ≤ -1 / 32 :=
        max_le (by linarith) (by linarith)
      rw [abs_of_neg (by linarith)]
      linarith
    by_cases hA4 : v < -155 / 64
    · refine habs (17 / 100) (29 / 100) (27 / 64) (lgamma_chord (-v) (by linarith) (by linarith))
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ (by norm_num) (by norm_num)
      rw [hfr]
      have : |v + 3 - 1 / 2| ≤ 5 / 64 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    · apply hrel
      have := GammaConvex.convex_right hcv (mem v h3 h2) (mem (-5 / 2) (by norm_num) (by norm_num))
        (by linarith : (-155 / 64 : ℝ) ≤ v) (by norm_num) (by linarith) (by linarith)
      rw [abs_of_pos (by linarith)]
      linarith

#print axioms s_ge
#print axioms lgamma_chord
#print axioms refl_four

end Library.Numerics.Float64.Lgamma.LgammaReflWin
