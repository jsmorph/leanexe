import Library.Numerics.Float64.Tgamma.TgammaMainRed
import Library.Numerics.Float64.Tgamma.TgammaMainPoly
import Library.Numerics.Float64.Tgamma.TgammaMainLoop
import Library.Numerics.Float64.Tgamma.TgammaRecipDD
import Library.Numerics.Float64.Tgamma.TgammaBranches
import LeanExe.ProofKit.GammaBasic

/-!
**The path of `tgammaWith` on `(-3, 4)`** within one step of `Γ`.  With `I = roundEven (x - 7/2)`,
`J = -I`, and `d = x - (I + 7/2)` (`TgammaMainRed.main_red`), `Γ x = Γ (7/2 + d) / W` for
`W = x (x + 1) ⋯ (x + J - 1)` (`GammaBasic.gamma_eq_div`).  The double-double polynomial lies within
`2 ^ -72` of `mainPoly d` (`TgammaMainPoly.main_poly`), which `MainFact` puts within `2 ^ -62` of
`Γ (7/2 + d) ≥ 1`.  The shift loop gives `W` within `2 ^ -80` relative (`TgammaMainLoop.loop_inv`),
the corrected reciprocal gives `1/W` within `2 ^ -77` (`TgammaRecipDD.recip_dd`), and their product
adds `2 ^ -70` (`prod_loose`), so the rounded `fh + (fl + eps)` is the nearest double to a value
within `2 ^ -60` of `Γ x` relative (`mainPath_within`).  When the rounding test of the code fails,
the result is that of the accurate path, which the theorem takes as a hypothesis.
-/

namespace Library.Numerics.Float64.Tgamma.TgammaMainPath
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD TgammaMul TgammaExpr TgammaWords
  TgammaMainRed TgammaMainPoly TgammaMainLoop TgammaRecipDD TgammaFloor TgammaRecip

set_option exponentiation.threshold 4096

/-- The product state after the shift loop. -/
def wState (x i : Float) : Float × Float × Float × Float :=
  if i.abs > 0.0 then
    LeanExe.loop (i.abs - 1.0).toUInt64 (x, (0.0 : Float), x, (0.0 : Float)) fun _ s => body s
  else ((1.0 : Float), (0.0 : Float), x, (0.0 : Float))

/-- The path on `(-3, 4)` with the shift loop as `wState`.  With the tail written as `evalF flE d`,
the definitional check of `rfl` exceeds the heartbeat limit, so the equation keeps the code's tail
and `fl_eq` rewrites it afterwards. -/
theorem mainPath_gen (dbTab accTab tab : Array UInt64) (x : Float) :
    TgammaBranches.mainPath dbTab accTab tab x =
      (let i := roundEven (x - 3.5)
       let d := x - (i + 3.5)
       let d2 := d * d
       let d4 := d2 * d2
       let fl := d * ((entry tab 46 + d * entry tab 47) +
         d2 * (entry tab 48 + d * entry tab 49) +
         d4 * ((entry tab 50 + d * entry tab 51) +
           d2 * (entry tab 52 + d * entry tab 53)))
       let (fh, fl) := polyDDD tab 0 10 d fl
       let (wh, wl, _, _) := wState x i
       let rh := 1.0 / wh
       let (fh, fl) := mulDD rh ((Library.Numerics.Arithmetic.Fma.Fma.fma rh (-wh) 1.0 - wl * rh) * rh) fh fl
       let eps := fh * Float.ofBits 0x3B92E3B40A0E9B4F
       let ub := fh + (fl + eps)
       let lb := fh + (fl - eps)
       if ub != lb then accurate accTab dbTab x else ub) := rfl

theorem fl_eq (d : Float) :
    evalF flE d = d * ((entry mainTable 46 + d * entry mainTable 47) +
      d * d * (entry mainTable 48 + d * entry mainTable 49) +
      d * d * (d * d) * ((entry mainTable 50 + d * entry mainTable 51) +
        d * d * (entry mainTable 52 + d * entry mainTable 53))) := by
  simp only [evalF, flE, pairE, d2E, d4E]
  rfl

theorem gamma_ge_one {y : ℝ} (hy : 2 ≤ y) : 1 ≤ Real.Gamma y := by
  have := Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr (le_refl (2 : ℝ)))
    (Set.mem_Ici.mpr hy) hy
  rwa [Real.Gamma_two] at this

theorem gamma_le_24 {y : ℝ} (hy2 : 2 ≤ y) (hy : y ≤ 5) : Real.Gamma y ≤ 24 := by
  have := Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr hy2)
    (Set.mem_Ici.mpr (by norm_num : (2 : ℝ) ≤ 5)) hy
  have h5 : Real.Gamma 5 = 24 := by
    rw [show (5 : ℝ) = (4 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    norm_num [Nat.factorial]
  linarith

/-- A non-integer double of magnitude at least `1/4` lies at least `2 ^ -54` from every integer. -/
theorem x_gap (x : Float) (hx : Finite x.toBits) (h4 : 1 / 4 ≤ |value x.toBits|)
    (hint : ∀ n : ℤ, value x.toBits ≠ n) (k : ℕ) : 1 / 2 ^ 54 ≤ |value x.toBits + k| := by
  obtain ⟨K, hK⟩ := grid x.toBits hx 1019 (by norm_num) (by norm_num; linarith)
  have hKv : (K : ℝ) = value x.toBits * 2 ^ 54 := by
    have h' : (K : ℝ) * 2 ^ 1020 = value x.toBits * 2 ^ 54 * 2 ^ 1020 := by
      linear_combination -1 * hK
    exact mul_right_cancel₀ (by positivity) h'
  have hz : K + (k : ℤ) * 2 ^ 54 ≠ 0 := by
    intro h0
    apply hint (-(k : ℤ))
    have : (K : ℝ) + (k : ℝ) * 2 ^ 54 = 0 := by exact_mod_cast h0
    push_cast
    linarith
  have h1 : (1 : ℝ) ≤ |((K + (k : ℤ) * 2 ^ 54 : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hz
  have e : ((K + (k : ℤ) * 2 ^ 54 : ℤ) : ℝ) = (value x.toBits + k) * 2 ^ 54 := by
    push_cast
    rw [hKv]
    ring
  rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ 54)] at h1
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- The product state: `wh + wl` approximates `x (x + 1) ⋯ (x + J - 1)` for `J = -I`. -/
theorem w_spec (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (x : Float) (hx : Finite x.toBits)
    (h1 : -3 < value x.toBits) (hgap : ∀ k : ℕ, 1 / 2 ^ 54 ≤ |value x.toBits + k|) (i : Float)
    (I : ℤ) (hi : Finite i.toBits) (hiv : value i.toBits = I) (hI7 : -7 ≤ I) (hI0 : I ≤ 0)
    (hxI : value x.toBits - I ≤ 4 + 1 / 2 ^ 50) :
    Finite (wState x i).1.toBits ∧ Finite (wState x i).2.1.toBits ∧
      |value (wState x i).1.toBits + value (wState x i).2.1.toBits -
          ∏ j ∈ Finset.range (-I).toNat, (value x.toBits + j)| ≤
        6 / 2 ^ 83 * |∏ j ∈ Finset.range (-I).toNat, (value x.toBits + j)| ∧
      |value (wState x i).2.1.toBits| ≤ 6 / 2 ^ 46 * |value (wState x i).1.toBits| := by
  obtain ⟨-, -, htest, hcount⟩ := count_spec i I hi hiv hI7 hI0
  by_cases hneg : I < 0
  · rw [wState, ite_eq_left (htest.mpr hneg), hcount hneg]
    have hn6 : (-I - 1).toNat ≤ 6 := by omega
    have hcast : (((-I - 1).toNat : ℕ) : ℝ) = -I - 1 := by
      have : (((-I - 1).toNat : ℤ) : ℝ) = ((-I - 1 : ℤ) : ℝ) := by
        rw [Int.toNat_of_nonneg (by omega)]
      push_cast at this
      exact this
    obtain ⟨f1, f2, -, -, hW, hk, -⟩ := loop_inv hF x hx h1 hgap _ hn6
      (by rw [hcast]; linarith [(by norm_num : (4 : ℝ) + 1 / 2 ^ 50 - 1 ≤ 7 / 2)])
    have hJ : (-I).toNat = (-I - 1).toNat + 1 := by omega
    have hn6' : (((-I - 1).toNat : ℕ) : ℝ) ≤ 6 := by exact_mod_cast hn6
    rw [hJ]
    refine ⟨f1, f2, hW.trans ?_, hk.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn6' (by positivity))
        (abs_nonneg _)
    · exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hn6' (by positivity))
        (abs_nonneg _)
  · rw [wState, ite_eq_right (mt htest.mp hneg)]
    have hI : I = 0 := by omega
    rw [hI]
    dsimp only
    rw [one_value, zero_value]
    refine ⟨one_finite, zero_finite, ?_, ?_⟩
    · norm_num
    · norm_num

/-- The magnitudes of the high parts, for the final product. -/
theorem mag_loose (vxph vxpl vwh vwl F W η θ κ : ℝ) (hP : |vxph + vxpl - F| ≤ η * |F|)
    (hp : |vxpl| ≤ |F| / 2 ^ 36) (hWc : |vwh + vwl - W| ≤ θ * |W|) (hk : |vwl| ≤ κ * |vwh|)
    (hη : η ≤ 1 / 2 ^ 60) (hθ : θ ≤ 1 / 2 ^ 60) (hκ : κ ≤ 1 / 2 ^ 36) :
    |F| * (1 - 1 / 2 ^ 35) ≤ |vxph| ∧ |vxph| ≤ |F| * (1 + 1 / 2 ^ 35) ∧
      |W| * (1 - 1 / 2 ^ 35) ≤ |vwh| ∧ |vwh| ≤ |W| * (1 + 1 / 2 ^ 35) := by
  have hF0 : 0 ≤ |F| := abs_nonneg F
  have hW0 : 0 ≤ |W| := abs_nonneg W
  have hb0 : 0 ≤ |vwh| := abs_nonneg _
  have heF : η * |F| ≤ 1 / 2 ^ 60 * |F| := mul_le_mul_of_nonneg_right hη hF0
  have hθW : θ * |W| ≤ 1 / 2 ^ 60 * |W| := mul_le_mul_of_nonneg_right hθ hW0
  have hκb : κ * |vwh| ≤ 1 / 2 ^ 36 * |vwh| := mul_le_mul_of_nonneg_right hκ hb0
  have hxF : |vxph - F| ≤ |F| / 2 ^ 35 := by
    have h := abs_sub (vxph + vxpl - F) vxpl
    rw [show vxph + vxpl - F - vxpl = vxph - F by ring] at h
    linarith only [h, hP, hp, heF, hF0]
  have hwW : |vwh - W| ≤ |W| / 2 ^ 60 + κ * |vwh| := by
    have h := abs_sub (vwh + vwl - W) vwl
    rw [show vwh + vwl - W - vwl = vwh - W by ring] at h
    linarith only [h, hWc, hk, hθW]
  have h1 := abs_sub_abs_le_abs_sub F vxph
  have h2 := abs_sub_abs_le_abs_sub vxph F
  have h3 := abs_sub_abs_le_abs_sub W vwh
  have h4 := abs_sub_abs_le_abs_sub vwh W
  rw [abs_sub_comm F] at h1
  rw [abs_sub_comm W] at h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith only [h1, hxF]
  · linarith only [h2, hxF]
  · linarith only [h3, hwW, hκb, hW0, hb0]
  · linarith only [h4, hwW, hκb, hW0]

/-- **The final product** `mulDD` with looser relative bounds than `prod_step`. -/
theorem prod_loose (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (xph xpl wh wl : Float) (hph : Finite xph.toBits)
    (hpl : Finite xpl.toBits) (hwh : Finite wh.toBits) (hwl : Finite wl.toBits) (F W η θ κ : ℝ)
    (hP : |value xph.toBits + value xpl.toBits - F| ≤ η * |F|)
    (hp : |value xpl.toBits| ≤ |F| / 2 ^ 36)
    (hWc : |value wh.toBits + value wl.toBits - W| ≤ θ * |W|)
    (hk : |value wl.toBits| ≤ κ * |value wh.toBits|)
    (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2 ^ 60) (hθ : θ ≤ 1 / 2 ^ 60) (hκ0 : 0 ≤ κ)
    (hκ : κ ≤ 1 / 2 ^ 36) (hlo : 1 / 2 ^ 900 ≤ |F| * |W|) (hhi : |F| * |W| ≤ 2 ^ 500) :
    Finite (mulDD xph xpl wh wl).1.toBits ∧ Finite (mulDD xph xpl wh wl).2.toBits ∧
      |value (mulDD xph xpl wh wl).1.toBits + value (mulDD xph xpl wh wl).2.toBits - F * W| ≤
        (η + θ + 1 / 2 ^ 70) * (|F| * |W|) ∧
      |value (mulDD xph xpl wh wl).2.toBits| ≤ |value (mulDD xph xpl wh wl).1.toBits| / 2 ^ 34 := by
  obtain ⟨ha_lo, ha_hi, hb_lo, hb_hi⟩ := mag_loose _ _ _ _ F W η θ κ hP hp hWc hk hη hθ hκ
  obtain ⟨PV, hPV⟩ : ∃ PV, PV = value xph.toBits + value xpl.toBits := ⟨_, rfl⟩
  obtain ⟨WV, hWV⟩ : ∃ WV, WV = value wh.toBits + value wl.toBits := ⟨_, rfl⟩
  rw [← hPV] at hP
  rw [← hWV] at hWc
  obtain ⟨a, ha⟩ : ∃ a, a = |value xph.toBits| := ⟨_, rfl⟩
  obtain ⟨p, hpd⟩ : ∃ p, p = |value xpl.toBits| := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = |value wh.toBits| := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = |value wl.toBits| := ⟨_, rfl⟩
  rw [← ha] at ha_lo ha_hi
  rw [← hb] at hb_lo hb_hi
  rw [← hpd] at hp
  rw [← hq, ← hb] at hk
  have ha0 : 0 ≤ a := ha ▸ abs_nonneg _
  have hp0 : 0 ≤ p := hpd ▸ abs_nonneg _
  have hb0 : 0 ≤ b := hb ▸ abs_nonneg _
  have hF0 : 0 ≤ |F| := abs_nonneg F
  have hW0 : 0 ≤ |W| := abs_nonneg W
  have hFW0 : 0 ≤ |F| * |W| := mul_nonneg hF0 hW0
  have hH0lo : |F| * |W| * ((1 - 1 / 2 ^ 35) * (1 - 1 / 2 ^ 35)) ≤ b * a := by
    calc |F| * |W| * ((1 - 1 / 2 ^ 35) * (1 - 1 / 2 ^ 35)) =
        (|W| * (1 - 1 / 2 ^ 35)) * (|F| * (1 - 1 / 2 ^ 35)) := by ring
      _ ≤ b * a := mul_le_mul hb_lo ha_lo (mul_nonneg hF0 (by norm_num)) hb0
  have hH0hi : b * a ≤ |F| * |W| * ((1 + 1 / 2 ^ 35) * (1 + 1 / 2 ^ 35)) := by
    calc b * a ≤ (|W| * (1 + 1 / 2 ^ 35)) * (|F| * (1 + 1 / 2 ^ 35)) :=
          mul_le_mul hb_hi ha_hi ha0 (mul_nonneg hW0 (by norm_num))
      _ = _ := by ring
  have hbF : b * |F| ≤ |F| * |W| * (1 + 1 / 2 ^ 35) := by
    calc b * |F| ≤ (|W| * (1 + 1 / 2 ^ 35)) * |F| := mul_le_mul_of_nonneg_right hb_hi hF0
      _ = _ := by ring
  have hbF' : b * (|F| * (1 - 1 / 2 ^ 35)) ≤ b * a := mul_le_mul_of_nonneg_left ha_lo hb0
  have hP1 : b * p ≤ b * (|F| / 2 ^ 36) := mul_le_mul_of_nonneg_left hp hb0
  have hP2 : q * a ≤ κ * b * a := mul_le_mul_of_nonneg_right hk ha0
  have hP2' : κ * b * a ≤ 1 / 2 ^ 36 * (b * a) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right hκ (mul_nonneg hb0 ha0)
  have hL2 : q * p ≤ κ * b * (|F| / 2 ^ 36) := mul_le_mul hk hp hp0 (mul_nonneg hκ0 hb0)
  have hL2' : κ * b * (|F| / 2 ^ 36) ≤ 1 / 2 ^ 36 * (b * |F|) / 2 ^ 36 := by
    have := mul_le_mul_of_nonneg_right hκ (mul_nonneg hb0 hF0)
    rw [show κ * b * (|F| / 2 ^ 36) = κ * (b * |F|) / 2 ^ 36 by ring]
    exact div_le_div_of_nonneg_right this (by positivity)
  have hHmax : b * a ≤ 2 ^ 900 := by linarith only [hH0hi, hhi]
  have hPmax : b * p + q * a ≤ 2 ^ 900 := by
    linarith only [hP1, hbF, hP2, hP2', hH0hi, hhi]
  obtain ⟨h1, h2, herr, hlow, -⟩ := mulDD_spec hF xph xpl wh wl hph hpl hwh hwl (b * a) (b * p)
    (q * a) (q * p) (le_of_eq (by rw [ha, hb])) (le_of_eq (by rw [hpd, hb]))
    (le_of_eq (by rw [hq, ha])) (le_of_eq (by rw [hq, hpd])) hHmax hPmax
  rw [← hPV, ← hWV] at herr
  have htiny : (1 : ℝ) / 2 ^ 1070 ≤ (|F| * |W|) / 2 ^ 170 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    linarith only [hlo]
  refine ⟨h1, h2, ?_, ?_⟩
  · have hEm : q * p + (4 * (b * p + q * a) + b * a / 2 ^ 51) / 2 ^ 53 + 1 / 2 ^ 1070 ≤
        (|F| * |W|) / 2 ^ 71 := by
      linarith only [hL2, hL2', hP1, hbF, hP2, hP2', hH0hi, htiny, hFW0]
    have hWVb : |WV| ≤ |W| * (1 + 1 / 2 ^ 60) := by
      have h5 := abs_sub_abs_le_abs_sub WV W
      have h6 := mul_le_mul_of_nonneg_right hθ hW0
      linarith only [h5, h6, hWc]
    have e1 : |PV - F| * |WV| ≤ (η * |F|) * (|W| * (1 + 1 / 2 ^ 60)) :=
      mul_le_mul hP hWVb (abs_nonneg _) (mul_nonneg hη0 hF0)
    have e2 : |F| * |WV - W| ≤ |F| * (θ * |W|) := mul_le_mul_of_nonneg_left hWc hF0
    have e3 : |PV * WV - F * W| ≤ |PV - F| * |WV| + |F| * |WV - W| := by
      rw [show PV * WV - F * W = (PV - F) * WV + F * (WV - W) by ring, ← abs_mul, ← abs_mul]
      exact abs_add_le _ _
    have e4 : η * (|F| * |W|) ≤ 1 / 2 ^ 60 * (|F| * |W|) := mul_le_mul_of_nonneg_right hη hFW0
    have e5 := abs_add_le
      (value (mulDD xph xpl wh wl).1.toBits + value (mulDD xph xpl wh wl).2.toBits - PV * WV)
      (PV * WV - F * W)
    rw [show value (mulDD xph xpl wh wl).1.toBits + value (mulDD xph xpl wh wl).2.toBits -
        PV * WV + (PV * WV - F * W) =
        value (mulDD xph xpl wh wl).1.toBits + value (mulDD xph xpl wh wl).2.toBits - F * W by
      ring] at e5
    linarith only [e5, herr, hEm, e3, e1, e2, e4, hFW0]
  · have hm := fapprox_mul (fapprox_self wh hwh) (fapprox_self xph hph) b a (le_of_eq hb.symm)
      (le_of_eq ha.symm) (b * a) (by simp) (by linarith only [hHmax])
    have hv1 : b * a * (1 - 1 / 2 ^ 53) - 1 / 2 ^ 1075 ≤ |value (mulDD xph xpl wh wl).1.toBits| := by
      have h := hm.2
      have h' := abs_sub_abs_le_abs_sub (value wh.toBits * value xph.toBits)
        (value (wh * xph).toBits)
      rw [abs_mul, ← ha, ← hb, abs_sub_comm] at h'
      show b * a * (1 - 1 / 2 ^ 53) - 1 / 2 ^ 1075 ≤ |value (wh * xph).toBits|
      simp only [zero_mul, mul_zero, add_zero, zero_add] at h
      linarith only [h, h']
    have hbalo : 1 / 2 ^ 1000 ≤ b * a := by
      have := mul_le_mul_of_nonneg_right hlo
        (by norm_num : (0 : ℝ) ≤ (1 - 1 / 2 ^ 35) * (1 - 1 / 2 ^ 35))
      linarith only [this, hH0lo]
    have hκba : 0 ≤ κ * b * a := mul_nonneg (mul_nonneg hκ0 hb0) ha0
    linarith only [hlow, hP1, hbF', hP2, hP2', hv1, hbalo, hκba]

theorem epsc_finite : Finite (Float.ofBits 0x3B92E3B40A0E9B4F).toBits :=
  ofBits_finite _ (by decide)

theorem epsc_le : |value (Float.ofBits 0x3B92E3B40A0E9B4F).toBits| ≤ 1 / 2 ^ 69 := by
  rw [ofBits_value _ (by decide)]
  have := TgammaSmall.abs_rat_le _ (1 / 2 ^ 69)
    (show PolyBound.qabs (PolyBound.ratOfWord 0x3B92E3B40A0E9B4F) ≤ 1 / 2 ^ 69 by decide +kernel)
  push_cast at this
  exact this

/-- **The path on `(-3, 4)`** within one step of `Γ`, when the accurate path is. -/
theorem mainPath_within (hF : Library.Numerics.Arithmetic.Fma.FmaSpec.FmaNearest) (hM : TgammaApprox.MainFact)
    (dbTab accTab : Array UInt64) (x : Float) (hx : Finite x.toBits)
    (h1 : -3 < value x.toBits) (h2 : value x.toBits < 4) (h4 : 1 / 4 ≤ |value x.toBits|)
    (hint : ∀ n : ℤ, value x.toBits ≠ n)
    (hacc : F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (accurate accTab dbTab x).toBits) :
    F64SignedRounding.WithinSteps 1 (Real.Gamma (value x.toBits))
      (TgammaBranches.mainPath dbTab accTab mainTable x).toBits := by
  rw [mainPath_gen]
  dsimp only
  obtain ⟨I, hI7, hI0, hif, hiv, -, -, hdf, hdv, hdb⟩ := main_red x hx h1 h2 h4
  generalize roundEven (x - 3.5) = i at hif hiv hdf hdv ⊢
  generalize x - (i + 3.5) = d at hdf hdv ⊢
  rw [← fl_eq d]
  have hgap := x_gap x hx h4 hint
  set vx := value x.toBits with hvx
  -- the polynomial and `G3 = Γ (7/2 + d)`
  have hdb' : |value d.toBits| ≤ 1 / 2 + 1 / 2 ^ 50 := by rw [hdv]; exact hdb
  obtain ⟨hpf1, hpf2, hpe, hpl⟩ := main_poly hF d hdf hdb'
  generalize polyDDD mainTable 0 10 d (evalF flE d) = p at hpf1 hpf2 hpe hpl ⊢
  obtain ⟨fh, fl⟩ := p
  dsimp only at hpf1 hpf2 hpe hpl ⊢
  have hG3 := hM (value d.toBits) hdb'
  obtain ⟨G3, hG3d⟩ : ∃ G, G = Real.Gamma (7 / 2 + value d.toBits) := ⟨_, rfl⟩
  rw [← hG3d] at hG3
  obtain ⟨hdb1, hdb2⟩ := abs_le.mp hdb'
  have hG3lo : 1 ≤ G3 := by rw [hG3d]; exact gamma_ge_one (by linarith)
  have hG3hi : G3 ≤ 24 := by rw [hG3d]; exact gamma_le_24 (by linarith) (by linarith)
  have hG3a : |G3| = G3 := abs_of_pos (by linarith)
  have hpG : |value fh.toBits + value fl.toBits - G3| ≤ (1 / 2 ^ 62 + 1 / 2 ^ 72) * |G3| := by
    rw [hG3a]
    have := abs_sub (value fh.toBits + value fl.toBits - TgammaApprox.mainPoly (value d.toBits))
      (G3 - TgammaApprox.mainPoly (value d.toBits))
    rw [show value fh.toBits + value fl.toBits - TgammaApprox.mainPoly (value d.toBits) -
      (G3 - TgammaApprox.mainPoly (value d.toBits)) = value fh.toBits + value fl.toBits - G3 by
      ring] at this
    linarith
  have hpk : |value fl.toBits| ≤ 1 / 2 ^ 41 * |value fh.toBits| := by
    have h5 := abs_sub_abs_le_abs_sub G3 (value fh.toBits + value fl.toBits)
    rw [abs_sub_comm G3, hG3a] at h5
    have h6 := abs_add_le (value fh.toBits) (value fl.toBits)
    rw [hG3a] at hpG
    linarith
  -- the product `W` and `Γ x = G3 / W`
  have hxI : vx - I = 7 / 2 + value d.toBits := by rw [hdv]; ring
  obtain ⟨wf1, wf2, hwe, hwk⟩ := w_spec hF x hx h1 hgap i I hif hiv hI7 hI0
    (by rw [hxI]; linarith)
  generalize wState x i = w at wf1 wf2 hwe hwk ⊢
  obtain ⟨wh, wl, w3, w4⟩ := w
  dsimp only at wf1 wf2 hwe hwk ⊢
  set W := ∏ j ∈ Finset.range (-I).toNat, (vx + j) with hWdef
  have hJ : (((-I).toNat : ℕ) : ℝ) = -I := by
    have : (((-I).toNat : ℤ) : ℝ) = ((-I : ℤ) : ℝ) := by rw [Int.toNat_of_nonneg (by omega)]
    push_cast at this
    exact this
  have hNP : GammaBasic.NotPole vx := fun m hm => hint (-(m : ℤ)) (by simp [hm])
  have hGW : Real.Gamma vx = G3 / W := by
    rw [GammaBasic.gamma_eq_div hNP (-I).toNat, hJ, hG3d, ← hxI, sub_eq_add_neg]
  have hJ7 : (-I).toNat ≤ 7 := by omega
  have hWabs : |W| = ∏ j ∈ Finset.range (-I).toNat, |vx + j| := by rw [hWdef, Finset.abs_prod]
  have hW_lo : 1 / 2 ^ 378 ≤ |W| := by
    rw [hWabs]
    calc (1 : ℝ) / 2 ^ 378 = (1 / 2 ^ 54) ^ 7 := by norm_num
      _ ≤ (1 / 2 ^ 54) ^ ((-I).toNat) := pow_le_pow_of_le_one (by positivity) (by norm_num) hJ7
      _ = ∏ j ∈ Finset.range (-I).toNat, (1 / 2 ^ 54 : ℝ) := by
        rw [Finset.prod_const, Finset.card_range]
      _ ≤ _ := Finset.prod_le_prod (fun j _ => by positivity) (fun j _ => hgap j)
  have hW_hi : |W| ≤ 2 ^ 14 := by
    rw [hWabs]
    calc ∏ j ∈ Finset.range (-I).toNat, |vx + j| ≤ ∏ j ∈ Finset.range (-I).toNat, (4 : ℝ) :=
          Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j hj => by
            have hj1 : ((j + 1 : ℕ) : ℝ) ≤ (((-I).toNat : ℕ) : ℝ) := by
              exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
            push_cast at hj1
            rw [hJ] at hj1
            have := Nat.cast_nonneg (α := ℝ) j
            rw [abs_le]
            constructor <;> linarith)
      _ = 4 ^ ((-I).toNat) := by rw [Finset.prod_const, Finset.card_range]
      _ ≤ 4 ^ 7 := pow_le_pow_right₀ (by norm_num) hJ7
      _ = 2 ^ 14 := by norm_num
  have hW0 : 0 < |W| := lt_of_lt_of_le (by positivity) hW_lo
  have hWne : W ≠ 0 := abs_pos.mp hW0
  set G := Real.Gamma vx with hGdef
  have hGabs : |G| = G3 / |W| := by rw [hGW, abs_div, hG3a]
  have hG_lo : 1 / 2 ^ 14 ≤ |G| := by
    rw [hGabs, le_div_iff₀ hW0]
    linarith
  have hG_hi : |G| ≤ 2 ^ 383 := by
    rw [hGabs, div_le_iff₀ hW0]
    linarith [(by norm_num : (2 : ℝ) ^ 383 * (1 / 2 ^ 378) = 32)]
  -- the reciprocal of `wh + wl`
  have hwk' : |value wl.toBits| ≤ |value wh.toBits| / 2 ^ 40 := by
    have := abs_nonneg (value wh.toBits)
    linarith
  have hw1 : |W| / 2 ≤ |value wh.toBits| ∧ |value wh.toBits| ≤ 2 * |W| := by
    have h5 := abs_sub_abs_le_abs_sub (value wh.toBits + value wl.toBits) W
    have h6 := abs_sub_abs_le_abs_sub W (value wh.toBits + value wl.toBits)
    rw [abs_sub_comm W] at h6
    have h7 := abs_add_le (value wh.toBits) (value wl.toBits)
    have h8 := abs_sub_abs_le_abs_sub (value wh.toBits + value wl.toBits) (value wl.toBits)
    rw [add_sub_cancel_right] at h8
    have h9 := abs_sub (value wh.toBits + value wl.toBits) (value wl.toBits)
    rw [add_sub_cancel_right] at h9
    constructor <;> linarith
  obtain ⟨hw1a, hw1b⟩ := hw1
  obtain ⟨hrf, hcf, hre, hcb, hrb⟩ := recip_dd hF wh wl wf1 wf2 hwk'
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 600 ≤ 1 / 2 ^ 378 / 2)])
    (by linarith [(by norm_num : (2 : ℝ) * 2 ^ 14 ≤ 2 ^ 600)])
  generalize (Library.Numerics.Arithmetic.Fma.Fma.fma (1.0 / wh) (-wh) 1.0 - wl * (1.0 / wh)) * (1.0 / wh) = c
    at hcf hre hcb ⊢
  generalize 1.0 / wh = rh at hrf hre hcb hrb ⊢
  obtain ⟨D, hD⟩ : ∃ D, D = value wh.toBits + value wl.toBits := ⟨_, rfl⟩
  rw [← hD] at hre hrb hwe
  have hD_lo : |W| * (1 - 6 / 2 ^ 83) ≤ |D| := by
    have := abs_sub_abs_le_abs_sub W D
    rw [abs_sub_comm W] at this
    linarith
  have hD0 : 0 < |D| := lt_of_lt_of_le (by positivity) hD_lo
  have hDne : D ≠ 0 := abs_pos.mp hD0
  have hiD : |1 / D| = 1 / |D| := by rw [abs_div, abs_one]
  have hiW : |1 / W| = 1 / |W| := by rw [abs_div, abs_one]
  have hiD_le : |1 / D| ≤ |1 / W| * (1 + 1 / 2 ^ 79) := by
    rw [hiD, hiW, show 1 / |W| * (1 + 1 / 2 ^ 79) = (1 + 1 / 2 ^ 79) / |W| by ring,
      div_le_div_iff₀ hD0 hW0]
    linarith
  have hDne' : |D| ≠ 0 := hD0.ne'
  have hiDW : |1 / D - 1 / W| ≤ 6 / 2 ^ 83 * |1 / D| := by
    rw [div_sub_div _ _ hDne hWne, abs_div, abs_mul, hiD, div_le_iff₀ (mul_pos hD0 hW0),
      show 6 / 2 ^ 83 * (1 / |D|) * (|D| * |W|) = 6 / 2 ^ 83 * |W| by field_simp]
    rw [show 1 * W - D * 1 = -(D - W) by ring, abs_neg]
    exact hwe
  have hiW0 : 0 ≤ |1 / W| := abs_nonneg _
  have hF1 : |value rh.toBits + value c.toBits - 1 / W| ≤ 1 / 2 ^ 77 * |1 / W| := by
    have := abs_add_le (value rh.toBits + value c.toBits - 1 / D) (1 / D - 1 / W)
    rw [show value rh.toBits + value c.toBits - 1 / D + (1 / D - 1 / W) =
      value rh.toBits + value c.toBits - 1 / W by ring] at this
    linarith
  have hcF : |value c.toBits| ≤ |1 / W| / 2 ^ 36 := by
    linarith
  -- the product `(rh + c) (p1 + p2)`
  have hFW : |1 / W| * |G3| = |G| := by rw [hGW, abs_div, abs_div, abs_one]; ring
  obtain ⟨hr1f, hr2f, hre2, hr21⟩ := prod_loose hF rh c fh fl hrf hcf hpf1 hpf2 (1 / W) G3
    (1 / 2 ^ 77) (1 / 2 ^ 62 + 1 / 2 ^ 72) (1 / 2 ^ 41) hF1 hcF hpG hpk (by positivity)
    (by norm_num) (by norm_num) (by positivity) (by norm_num) (by rw [hFW]; linarith)
    (by rw [hFW]; linarith)
  rw [hFW, show 1 / W * G3 = G by rw [hGW]; ring] at hre2
  generalize mulDD rh c fh fl = r at hr1f hr2f hre2 hr21 ⊢
  obtain ⟨r1, r2⟩ := r
  dsimp only at hr1f hr2f hre2 hr21 ⊢
  -- `eps` and the last rounding
  set v1 := value r1.toBits with hv1
  set v2 := value r2.toBits with hv2
  have hr1b : |G| / 2 ≤ |v1| ∧ |v1| ≤ 2 * |G| := by
    have h5 := abs_sub_abs_le_abs_sub (v1 + v2) G
    have h6 := abs_sub_abs_le_abs_sub G (v1 + v2)
    rw [abs_sub_comm G] at h6
    have h8 := abs_sub_abs_le_abs_sub (v1 + v2) v2
    rw [add_sub_cancel_right] at h8
    have h9 := abs_sub (v1 + v2) v2
    rw [add_sub_cancel_right] at h9
    have hG0 := abs_nonneg G
    constructor <;> linarith
  obtain ⟨hr1lo, hr1hi⟩ := hr1b
  have hem := fapprox_mul (fapprox_self r1 hr1f) (fapprox_self _ epsc_finite) |v1| (1 / 2 ^ 69)
    le_rfl epsc_le (|v1| * (1 / 2 ^ 69)) (by simp)
    (by linarith [(by norm_num : (2 : ℝ) * 2 ^ 383 * (1 / 2 ^ 69) < 2 ^ 1022)])
  have heb : |value (r1 * Float.ofBits 0x3B92E3B40A0E9B4F).toBits| ≤ |v1| / 2 ^ 68 := by
    have h := hem.2
    simp only [zero_mul, mul_zero, add_zero, zero_add] at h
    have h3 := abs_sub_abs_le_abs_sub (value (r1 * Float.ofBits 0x3B92E3B40A0E9B4F).toBits)
      (v1 * value (Float.ofBits 0x3B92E3B40A0E9B4F).toBits)
    have h4 : |v1 * value (Float.ofBits 0x3B92E3B40A0E9B4F).toBits| ≤ |v1| * (1 / 2 ^ 69) := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left epsc_le (abs_nonneg _)
    have htiny : (1 : ℝ) / 2 ^ 1075 ≤ |v1| / 2 ^ 1000 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  have hef := hem.1
  generalize r1 * Float.ofBits 0x3B92E3B40A0E9B4F = e at hef heb ⊢
  have ha := fapprox_add (fapprox_self r2 hr2f) (fapprox_self e hef) (|v2| + |value e.toBits|)
    (by simp only [add_zero]; exact abs_add_le _ _)
    (by linarith [(by norm_num : (2 : ℝ) * 2 ^ 383 < 2 ^ 1022)])
  have hae : |value (r2 + e).toBits - (v2 + value e.toBits)| ≤ |v1| / 2 ^ 86 := by
    have h := ha.2
    simp only [zero_add] at h
    linarith
  obtain ⟨S', hS'⟩ : ∃ S, S = v1 + value (r2 + e).toBits := ⟨_, rfl⟩
  have hS'G : |S' - G| ≤ 1 / 2 ^ 60 * |G| := by
    have hsplit : S' - G = (v1 + v2 - G) + value e.toBits +
        (value (r2 + e).toBits - (v2 + value e.toBits)) := by rw [hS']; ring
    rw [hsplit]
    have h3 := abs_add_le (v1 + v2 - G + value e.toBits)
      (value (r2 + e).toBits - (v2 + value e.toBits))
    have h4 := abs_add_le (v1 + v2 - G) (value e.toBits)
    linarith
  have hG0 : 0 < |G| := lt_of_lt_of_le (by positivity) hG_lo
  have hS'0 : v1 + value (r2 + e).toBits ≠ 0 := by
    rw [← hS']
    intro h0
    rw [h0, zero_sub, abs_neg] at hS'G
    linarith
  have hS'max : |v1 + value (r2 + e).toBits| < 2 ^ 1023 := by
    rw [← hS']
    have := abs_sub_abs_le_abs_sub S' G
    linarith [(by norm_num : (2 : ℝ) ^ 383 * (1 + 1 / 2 ^ 60) < 2 ^ 1023)]
  have hround := F64RoundNearest.add_rounded r1.toBits (r2 + e).toBits hr1f ha.1 hS'0 hS'max
  rw [← F64Bits.toBits_add, ← hS'] at hround
  have hwithin : F64SignedRounding.WithinSteps 1 G (r1 + (r2 + e)).toBits :=
    F64RoundNearest.within_one_of_rounded_rel _ S' G hround (1 / 2 ^ 60) (by positivity)
      (by norm_num) hS'G (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 1021 ≤ 1 / 2 ^ 14)])
      (by linarith [(by norm_num : (2 : ℝ) ^ 383 < 2 ^ 1022)])
  by_cases hc : (r1 + (r2 + e) != r1 + (r2 - e)) = true
  · rw [ite_eq_left hc]
    exact hacc
  · rw [ite_eq_right hc]
    exact hwithin

#print axioms x_gap
#print axioms w_spec
#print axioms prod_loose
#print axioms mainPath_within

end Library.Numerics.Float64.Tgamma.TgammaMainPath
