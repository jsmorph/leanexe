import Library.Numerics.Float64.Erfc.ErfcExp1Red
import Library.Numerics.Float64.Erfc.ErfcExpTab
import Library.Numerics.Float64.Erfc.ErfcQ1
import Library.Numerics.Float64.Erfc.ErfcCast

/-!
`exp_1` of `Erfc`: `exp (xh + xl)` for `-700 ≤ xh ≤ -8`.  With `K = -n` from the reduction
(`ErfcExp1Red.red_spec`), `-n = 4096 (m - 1023) + 64 i2 + i1` (`ErfcExpBits.split_k`), so
`exp (xh + xl) = 2^(m - 1023) 2^(i2/64) 2^(i1/4096) exp (Y)` up to the reduction's error, where
`2^(i1/4096)` and `2^(i2/64)` come from the tables (`ErfcExpTab.tab_sound`), `exp (Y)` from `q_1`
(`ErfcQ1`), and the products from `Erfc.dMul` (`ErfcTrack4.pr_dMul`).  The final products by
`2^(m - 1023)` are exact for the high part and add at most `u |lo| + 2^-1075` for the low part.
-/

namespace Library.Numerics.Float64.Erfc.ErfcExp1

open CodeLib.IEEE64 LeanExe.ProofKit ErfcEft ErfcEft2 ErfcOps ErfcTrack ErfcTrack2 ErfcTrack4 ErfcFastMain
  ErfcRound ErfcExpBits ErfcExp1Red ErfcExpTab ErfcQ1 Library.Numerics.Arithmetic.Fma.FmaSpec PolyBound

set_option exponentiation.threshold 2200

/-- `Erfc.exp1` with its constants as arguments. -/
def exp1Core (tab : Array UInt64) (C ch cl c4 c3 half one : Float) (xh xl : Float) :
    Float × Float :=
  let k := Erfc.roundEven (xh * C)
  let (kh, kl) := Erfc.sMul k ch cl
  let (yh, yl) := Erfc.fastTwoSum (xh - kh) xl
  let yl := yl - kl
  let kw := Erfc.toWord k
  let m := Erfc.sar kw 12 + 0x3ff
  let i2 := Erfc.sar kw 6 &&& 0x3f
  let i1 := kw &&& 0x3f
  let (hi, lo) := Erfc.dMul (Erfc.entry tab (128 + 2 * i1)) (Erfc.entry tab (128 + 2 * i1 + 1))
    (Erfc.entry tab (2 * i2)) (Erfc.entry tab (2 * i2 + 1))
  let (qh, ql) := q1Core c4 c3 half one yh yl
  let (hi, lo) := Erfc.dMul hi lo qh ql
  let d := Float.ofBits (m <<< 52)
  (hi * d, lo * d)

theorem exp1_eq (tab : Array UInt64) (xh xl : Float) :
    Erfc.exp1 tab xh xl = exp1Core tab (Float.ofBits 0x40B71547652B82FE)
      (Float.ofBits 0x3F262E42FEFA39EF) (Float.ofBits 0x3BBABC9E3B39803F)
      (Float.ofBits 0x3FA55555558489DC) (Float.ofBits 0x3FC5555555995D37) 0.5 1.0 xh xl := rfl

/-- The words of the tables are finite, and the low parts are small. -/
theorem tab_words : (∀ j < 256, Finite Erfc.expTable[j]!) ∧
    (∀ j < 128, |ratOfWord Erfc.expTable[2 * j]!| ≤ 2 ∧
      |ratOfWord Erfc.expTable[2 * j + 1]!| ≤ 1 / 2 ^ 52) := by
  decide +kernel

/-- A double-double entry of the tables as a `Pr` of `2^(j/n)`. -/
theorem tab_pr (base n j : ℕ) (hn : 1 ≤ n) (hj : base + 2 * j + 1 < 256) (hb : base % 2 = 0)
    (h : tabOK base n j = true) :
    Pr (Float.ofBits Erfc.expTable[base + 2 * j]!) (Float.ofBits Erfc.expTable[base + 2 * j + 1]!)
      (Real.exp (j * Real.log 2 / n)) (2 + 1 / 2 ^ 52 + 1 / 2 ^ 93) (1 / 2 ^ 52)
      (1 / 2 ^ 93) := by
  obtain ⟨hfin, hlow⟩ := tab_words
  have k1 := hlow (base / 2 + j) (by omega)
  rw [show 2 * (base / 2 + j) = base + 2 * j by omega] at k1
  obtain ⟨f1, v1⟩ := ofBits_ff _ (hfin (base + 2 * j) (by omega))
  obtain ⟨f2, v2⟩ := ofBits_ff _ (hfin (base + 2 * j + 1) (by omega))
  have hs := tab_sound base n j hn h
  have hv : fv (Float.ofBits Erfc.expTable[base + 2 * j]!) +
      fv (Float.ofBits Erfc.expTable[base + 2 * j + 1]!) = (tabV base j : ℝ) := by
    rw [v1, v2, tabV]; push_cast; ring
  have h1 : |(ratOfWord Erfc.expTable[base + 2 * j]! : ℝ)| ≤ 2 := by qc k1.1
  have h2 : |(ratOfWord Erfc.expTable[base + 2 * j + 1]! : ℝ)| ≤ 1 / 2 ^ 52 := by
    qc k1.2
  have htab : (tabV base j : ℝ) ≤ 2 + 1 / 2 ^ 52 := by
    rw [tabV]; push_cast
    linarith [le_abs_self (ratOfWord Erfc.expTable[base + 2 * j]! : ℝ),
      le_abs_self (ratOfWord Erfc.expTable[base + 2 * j + 1]! : ℝ)]
  have htab0 : (0 : ℝ) ≤ tabV base j := by
    have := (abs_le.mp hs).1
    have := Real.exp_pos (j * Real.log 2 / n)
    nlinarith
  have hsb : (1 / 2 ^ 95 : ℝ) * tabV base j ≤ 1 / 2 ^ 93 := by
    have : (1 / 2 ^ 95 : ℝ) * tabV base j ≤ 1 / 2 ^ 95 * (2 + 1 / 2 ^ 52) := by gcongr
    linarith [show (1 : ℝ) / 2 ^ 95 * (2 + 1 / 2 ^ 52) ≤ 1 / 2 ^ 93 by norm_num]
  refine ⟨f1, f2, ?_, ?_, ?_⟩
  · rw [hv]; exact hs.trans hsb
  · rw [abs_of_pos (Real.exp_pos _)]
    have := (abs_le.mp hs).1
    linarith
  · rw [v2]; exact h2

theorem exp_lower (X : ℝ) (hX : -701 ≤ X) : 1 / 2 ^ 1012 ≤ Real.exp X := by
  have h2 : (1 : ℝ) / 2 ^ 1012 = Real.exp (-(1012 * Real.log 2)) := by
    rw [Real.exp_neg, ← Real.log_rpow (by norm_num), Real.exp_log (by positivity)]
    norm_num
  rw [h2]
  apply Real.exp_le_exp.mpr
  have := Real.log_two_gt_d9
  linarith


/-- The final scaling of `exp_1` by `d = 2^(M - 1023)`. -/
theorem final_scale (hi lo d : Float) (V X : ℝ) (M : ℕ)
    (hp : Pr hi lo V (41 / 10) (1 / 2 ^ 35) (1 / 2 ^ 65))
    (hd : ff d ∧ fv d = 2 ^ M / 2 ^ 1023) (hdm : Wasm.IEEE64.scaledMagnitude d.toBits = 2 ^ (M + 51))
    (hM1 : 2 ≤ M) (hM2 : M ≤ 1022) (hV : 9998 / 10000 ≤ V)
    (hDV : |2 ^ M / 2 ^ 1023 * V - Real.exp X| ≤ 1 / 2 ^ 69 * Real.exp X) (hX : -701 ≤ X) :
    ff (hi * d) ∧ ff (lo * d) ∧
      |fv (hi * d) + fv (lo * d) - Real.exp X| ≤ 1 / 2 ^ 60 * Real.exp X ∧
      |fv (lo * d)| ≤ 1 / 2 ^ 30 * Real.exp X := by
  have hE := exp_lower X hX
  have hE0 : 0 < Real.exp X := Real.exp_pos X
  set D : ℝ := 2 ^ M / 2 ^ 1023 with hDdef
  have hD0 : 0 < D := by positivity
  have hDle : D ≤ 10003 / 10000 * Real.exp X := by
    have h1 : D * V ≤ (1 + 1 / 2 ^ 69) * Real.exp X := by linarith [(abs_le.mp hDV).2]
    have h2 : D * (9998 / 10000) ≤ D * V := by gcongr
    linarith
  obtain ⟨hf, lf, he, hMb, hL⟩ := hp
  have hhi1 : (1 / 2 : ℝ) ≤ |fv hi| := by
    have t1 := abs_sub_abs_le_abs_sub V (fv hi + fv lo)
    have t2 := abs_add_le (fv hi) (fv lo)
    rw [abs_sub_comm] at t1
    have hV' : (9998 / 10000 : ℝ) ≤ |V| := hV.trans (le_abs_self V)
    linarith [show (1 : ℝ) / 2 ^ 65 + 1 / 2 ^ 35 ≤ 1 / 4 by norm_num]
  have hhi2 : |fv hi| < 16 := by
    have : fv hi = (fv hi + fv lo - V) + V - fv lo := by ring
    rw [this]
    have := abs_sub_le' (fv hi + fv lo - V + V) (fv lo)
    have := abs_add_le (fv hi + fv lo - V) V
    linarith [show (1 : ℝ) / 2 ^ 65 + 41 / 10 + 1 / 2 ^ 35 < 16 by norm_num]
  have hg1 : 1021 ≤ gx hi.toBits := gx_ge _ _ (by
    rw [show (2 : ℝ) ^ (52 + 1021) / 2 ^ 1074 = 1 / 2 by norm_num]; exact hhi1)
  have hg2 : gx hi.toBits ≤ 1025 := gx_le_of_lt _ _ (by
    rw [show (2 : ℝ) ^ (53 + 1025) / 2 ^ 1074 = 16 by norm_num]; exact hhi2)
  obtain ⟨m1, mv⟩ := mul_pow2_right hi d hf hd.1 (M + 51) hdm (by omega) (by omega)
  have hlD : |fv lo * fv d| ≤ 1 := by
    rw [abs_mul, hd.2, abs_of_pos hD0]
    have : D ≤ 2 := by
      have : (2 : ℝ) ^ M ≤ 2 ^ 1022 := pow_le_pow_right₀ (by norm_num) hM2
      rw [hDdef]; rw [div_le_iff₀ (by positivity)]; linarith [show (2 : ℝ) ^ 1022 ≤ 2 * 2 ^ 1023 by norm_num]
    calc |fv lo| * D ≤ 1 / 2 ^ 35 * 2 := mul_le_mul hL this hD0.le (by norm_num)
      _ ≤ 1 := by norm_num
  obtain ⟨m2, merr⟩ := mul_f lo d lf hd.1 (hlD.trans (by norm_num))
  rw [hd.2] at mv merr hlD
  have hη : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 63 * Real.exp X := by
    have : (1 : ℝ) / 2 ^ 1075 = 1 / 2 ^ 63 * (1 / 2 ^ 1012) := by norm_num
    rw [this]; gcongr
  have hloD : |fv lo * D| ≤ 1 / 2 ^ 35 * (10003 / 10000 * Real.exp X) := by
    rw [abs_mul, abs_of_pos hD0]; exact mul_le_mul hL hDle hD0.le (by norm_num)
  refine ⟨m1, m2, ?_, ?_⟩
  · have e1 : fv (hi * d) + fv (lo * d) - Real.exp X = D * (fv hi + fv lo - V) +
        (fv (lo * d) - fv lo * D) + (D * V - Real.exp X) := by rw [mv]; ring
    rw [e1]
    have k1 : |D * (fv hi + fv lo - V)| ≤ 10003 / 10000 * Real.exp X * (1 / 2 ^ 65) := by
      rw [abs_mul, abs_of_pos hD0]; exact mul_le_mul hDle he (abs_nonneg _) (by positivity)
    have k2 : |fv (lo * d) - fv lo * D| ≤ 1 / 2 ^ 53 * (1 / 2 ^ 35 * (10003 / 10000 *
        Real.exp X)) + 1 / 2 ^ 63 * Real.exp X := by
      refine merr.trans ?_
      have : (1 / 2 ^ 53 : ℝ) * |fv lo * D| ≤ 1 / 2 ^ 53 * (1 / 2 ^ 35 * (10003 / 10000 *
          Real.exp X)) := by gcongr
      linarith
    have k3 := abs_add3 (D * (fv hi + fv lo - V)) (fv (lo * d) - fv lo * D) (D * V - Real.exp X)
    linarith
  · have k1 := abs_sub_abs_le_abs_sub (fv (lo * d)) (fv lo * D)
    have k2 : (1 / 2 ^ 53 : ℝ) * |fv lo * D| ≤ 1 / 2 ^ 53 * (1 / 2 ^ 35 * (10003 / 10000 *
        Real.exp X)) := by gcongr
    linarith

/-- `exp_1` within `2^-60` relative of `exp (xh + xl)` for `-700 ≤ xh ≤ -8`. -/
theorem exp1_err (hF : FmaNearest) (xh xl : Float) (hxh : ff xh) (hxl : ff xl)
    (h1 : -700 ≤ fv xh) (h2 : fv xh ≤ -8) (hxl' : |fv xl| ≤ 1 / 2 ^ 40) :
    ff (Erfc.exp1 Erfc.expTable xh xl).1 ∧ ff (Erfc.exp1 Erfc.expTable xh xl).2 ∧
      |fv (Erfc.exp1 Erfc.expTable xh xl).1 + fv (Erfc.exp1 Erfc.expTable xh xl).2 -
        Real.exp (fv xh + fv xl)| ≤ 1 / 2 ^ 60 * Real.exp (fv xh + fv xl) ∧
      |fv (Erfc.exp1 Erfc.expTable xh xl).2| ≤ 1 / 2 ^ 30 * Real.exp (fv xh + fv xl) := by
  obtain ⟨cf1, cf2, cf3, cv1, cv2, cv3⟩ := cw_vals
  obtain ⟨n, hn1, hn2, kf, kv, yhf, ylf, hY, hYb, hylb⟩ :=
    red_spec hF xh xl _ _ _ hxh hxl h1 h2 hxl' ⟨cf1, cv1⟩ ⟨cf2, cv2⟩ ⟨cf3, cv3⟩
  rw [exp1_eq]
  unfold exp1Core
  dsimp only
  set C := Float.ofBits 0x40B71547652B82FE
  set k := Erfc.roundEven (xh * C)
  set ch := Float.ofBits 0x3F262E42FEFA39EF
  set cl := Float.ofBits 0x3BBABC9E3B39803F
  set yh := (Erfc.fastTwoSum (xh - (Erfc.sMul k ch cl).1) xl).1
  set yl := (Erfc.fastTwoSum (xh - (Erfc.sMul k ch cl).1) xl).2 - (Erfc.sMul k ch cl).2
  -- the indices
  have hkw := toWord_neg k kf n kv hn1 (by omega)
  obtain ⟨hm, hi2, hi1, hsplit⟩ := split_k (Erfc.toWord k) n hn1 (by omega) hkw
  set j1 := 63 - (n - 1) % 64 with hj1
  set j2 := 63 - (n - 1) / 64 % 64 with hj2
  set M := 1022 - (n - 1) / 4096 with hM
  have hj1b : j1 < 64 := by omega
  have hj2b : j2 < 64 := by omega
  have hMb : 2 ≤ M ∧ M ≤ 1022 := by omega
  have ix1 : (128 + 2 * (Erfc.toWord k &&& 0x3f)).toNat = 128 + 2 * j1 := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, hi1]
    simp only [show (128 : UInt64).toNat = 128 from rfl, show (2 : UInt64).toNat = 2 from rfl]
    omega
  have ix2 : (128 + 2 * (Erfc.toWord k &&& 0x3f) + 1).toNat = 128 + 2 * j1 + 1 := by
    rw [UInt64.toNat_add, ix1, show (1 : UInt64).toNat = 1 from rfl]; omega
  have ix3 : (2 * (Erfc.sar (Erfc.toWord k) 6 &&& 0x3f)).toNat = 0 + 2 * j2 := by
    rw [UInt64.toNat_mul, hi2, show (2 : UInt64).toNat = 2 from rfl]; omega
  have ix4 : (2 * (Erfc.sar (Erfc.toWord k) 6 &&& 0x3f) + 1).toNat = 0 + 2 * j2 + 1 := by
    rw [UInt64.toNat_add, ix3, show (1 : UInt64).toNat = 1 from rfl]; omega
  rw [show Erfc.entry Erfc.expTable (128 + 2 * (Erfc.toWord k &&& 0x3f)) =
      Float.ofBits Erfc.expTable[128 + 2 * j1]! by unfold Erfc.entry; rw [ix1],
    show Erfc.entry Erfc.expTable (128 + 2 * (Erfc.toWord k &&& 0x3f) + 1) =
      Float.ofBits Erfc.expTable[128 + 2 * j1 + 1]! by unfold Erfc.entry; rw [ix2],
    show Erfc.entry Erfc.expTable (2 * (Erfc.sar (Erfc.toWord k) 6 &&& 0x3f)) =
      Float.ofBits Erfc.expTable[0 + 2 * j2]! by unfold Erfc.entry; rw [ix3],
    show Erfc.entry Erfc.expTable (2 * (Erfc.sar (Erfc.toWord k) 6 &&& 0x3f) + 1) =
      Float.ofBits Erfc.expTable[0 + 2 * j2 + 1]! by unfold Erfc.entry; rw [ix4]]
  -- the tables and their product
  have t2 := tab_pr 128 4096 j1 (by norm_num) (by omega) (by norm_num) (tab2_ok j1 hj1b)
  have t1 := tab_pr 0 64 j2 (by norm_num) (by omega) (by norm_num) (tab1_ok j2 hj2b)
  have p1 := pr_dMul hF t2 t1 (2 + 1 / 2 ^ 50) (2 + 1 / 2 ^ 50) (1 / 2 ^ 50) (1 / 2 ^ 49)
    (4 + 1 / 2 ^ 40) (1 / 2 ^ 48) (1 / 2 ^ 90) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- `q_1`
  have kq3 : ff (Float.ofBits 0x3FC5555555995D37) ∧
      fv (Float.ofBits 0x3FC5555555995D37) = q1Q.getD 0 0 :=
    ofBits_ff _ (by unfold CodeLib.IEEE64.Finite; decide +kernel)
  have kq4 : ff (Float.ofBits 0x3FA55555558489DC) ∧
      fv (Float.ofBits 0x3FA55555558489DC) = q1Q.getD 1 0 :=
    ofBits_ff _ (by unfold CodeLib.IEEE64.Finite; decide +kernel)
  have khalf : ff (0.5 : Float) ∧ fv (0.5 : Float) = 1 / 2 := by
    obtain ⟨a, b⟩ := ofBits_ff 0x3FE0000000000000 (by unfold CodeLib.IEEE64.Finite; decide +kernel)
    rw [show (0.5 : Float) = Float.ofBits 0x3FE0000000000000 by
      rw [← F64Bits.ofBits_toBits (0.5 : Float)]; rfl]
    exact ⟨a, by rw [b, show ratOfWord 0x3FE0000000000000 = 1 / 2 by decide +kernel]; norm_num⟩
  obtain ⟨k1f, k1v⟩ := one_val
  have hq := q1_core_pr hF _ _ _ _ yh yl yhf ylf (1 / 7000) (1 / 7000 + 1 / 2 ^ 40) (1 / 2 ^ 40)
    (by push_cast; exact hYb)
    (by
      have := abs_sub_le' (fv yh + fv yl) (fv yl)
      rw [show fv yh + fv yl - fv yl = fv yh by ring] at this
      push_cast; linarith)
    (by push_cast; exact hylb) (q1B q1Q (1 / 7000) (1 / 7000 + 1 / 2 ^ 40) (1 / 2 ^ 40))
    (by decide +kernel) kq3 kq4 khalf ⟨k1f, k1v⟩
  have hqe := q1_exp (fv yh) (fv yl) (fv (Float.ofBits 0x3FC5555555995D37))
    (fv (Float.ofBits 0x3FA55555558489DC)) (1 / 7000) (1 / 2 ^ 40) hYb (by norm_num) hylb
    (by rw [kq4.2]; have : (0 : ℚ) ≤ q1Q.getD 1 0 := by decide +kernel
        qc this)
  rw [kq3.2, kq4.2, khalf.2, k1v] at hq
  rw [kq3.2, kq4.2] at hqe
  have hqb : (1 / 7000 : ℝ) ^ 5 * (6 / 600) + (1 / 7000) ^ 3 * (|1 / 6 - ((q1Q.getD 0 0 : ℚ) : ℝ)| +
      1 / 7000 * |1 / 24 - ((q1Q.getD 1 0 : ℚ) : ℝ)| + ((q1Q.getD 1 0 : ℚ) : ℝ) * (1 / 2 ^ 40)) ≤
      1 / 2 ^ 68 := by
    have h : (1 / 7000 : ℚ) ^ 5 * (6 / 600) + (1 / 7000) ^ 3 * (|1 / 6 - q1Q.getD 0 0| +
        1 / 7000 * |1 / 24 - q1Q.getD 1 0| + q1Q.getD 1 0 * (1 / 2 ^ 40)) ≤ 1 / 2 ^ 68 := by
      decide +kernel
    qc h
  have hqb2 : (q1B q1Q (1 / 7000) (1 / 7000 + 1 / 2 ^ 40) (1 / 2 ^ 40)).sM ≤ 10002 / 10000 ∧
      (q1B q1Q (1 / 7000) (1 / 7000 + 1 / 2 ^ 40) (1 / 2 ^ 40)).sL ≤ 1 / 2 ^ 39 ∧
      (q1B q1Q (1 / 7000) (1 / 7000 + 1 / 2 ^ 40) (1 / 2 ^ 40)).se ≤ 1 / 2 ^ 77 := by
    decide +kernel
  obtain ⟨hsM, hsL, hse⟩ := hqb2
  have hq' := (hq.shift (Real.exp (fv yh + fv yl)) (1 / 2 ^ 68) (by
      rw [abs_sub_comm]
      exact hqe.trans hqb)
    (10002 / 10000 + 1 / 2 ^ 68) (1 / 2 ^ 77 + 1 / 2 ^ 68)
    (by have := (Rat.cast_le (K := ℝ)).mpr hsM; push_cast at this ⊢; linarith)
    (by have := (Rat.cast_le (K := ℝ)).mpr hse; push_cast at this ⊢; linarith)).mono
    (M' := 10002 / 10000 + 1 / 2 ^ 68) (L' := 1 / 2 ^ 39) (e' := 1 / 2 ^ 77 + 1 / 2 ^ 68) le_rfl
    (by have := (Rat.cast_le (K := ℝ)).mpr hsL; push_cast at this ⊢; linarith) le_rfl
  have p2 := pr_dMul hF p1 hq' (4 + 1 / 2 ^ 39) (1001 / 1000) (1 / 2 ^ 50) (1 / 2 ^ 36)
    (41 / 10) (1 / 2 ^ 35) (1 / 2 ^ 65) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hm1 : 1 ≤ (Erfc.sar (Erfc.toWord k) 12 + 0x3ff).toNat := by rw [hm]; omega
  have hm2 : (Erfc.sar (Erfc.toWord k) 12 + 0x3ff).toNat ≤ 2046 := by rw [hm]; omega
  have hd := pow2_word _ hm1 hm2
  have hdm := pow2_mag _ hm1 hm2
  rw [hm] at hd hdm
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Y := fv yh + fv yl with hYdef
  have hYlo : -(1 / 7000 : ℝ) ≤ Y := (abs_le.mp hYb).1
  have hV : (9998 / 10000 : ℝ) ≤ Real.exp ((j1 : ℝ) * Real.log 2 / ((4096 : ℕ) : ℝ)) *
      Real.exp ((j2 : ℝ) * Real.log 2 / ((64 : ℕ) : ℝ)) * Real.exp Y := by
    have e1 : 1 ≤ Real.exp ((j1 : ℝ) * Real.log 2 / ((4096 : ℕ) : ℝ)) :=
      Real.one_le_exp (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog0.le) (Nat.cast_nonneg _))
    have e2 : 1 ≤ Real.exp ((j2 : ℝ) * Real.log 2 / ((64 : ℕ) : ℝ)) :=
      Real.one_le_exp (div_nonneg (mul_nonneg (Nat.cast_nonneg _) hlog0.le) (Nat.cast_nonneg _))
    have e3 : 1 + Y ≤ Real.exp Y := by linarith [Real.add_one_le_exp Y]
    have e3' : (9998 / 10000 : ℝ) ≤ Real.exp Y := by linarith
    calc (9998 / 10000 : ℝ) = 1 * 1 * (9998 / 10000) := by ring
      _ ≤ _ := by gcongr
  have hDV : |2 ^ M / 2 ^ 1023 * (Real.exp ((j1 : ℝ) * Real.log 2 / ((4096 : ℕ) : ℝ)) *
      Real.exp ((j2 : ℝ) * Real.log 2 / ((64 : ℕ) : ℝ)) * Real.exp Y) -
      Real.exp (fv xh + fv xl)| ≤ 1 / 2 ^ 69 * Real.exp (fv xh + fv xl) := by
    have h2M : (2 : ℝ) ^ M / 2 ^ 1023 = Real.exp (((M : ℝ) - 1023) * Real.log 2) := by
      have hA : Real.exp ((M : ℝ) * Real.log 2) = 2 ^ M := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
      have hB : Real.exp ((1023 : ℝ) * Real.log 2) = 2 ^ 1023 := by
        have := Real.exp_nat_mul (Real.log 2) 1023
        push_cast at this
        rw [this, Real.exp_log (by norm_num)]
      rw [sub_mul, Real.exp_sub, hA, hB]
    have hs : ((M : ℝ) - 1023) * Real.log 2 + (j1 : ℝ) * Real.log 2 / ((4096 : ℕ) : ℝ) +
        (j2 : ℝ) * Real.log 2 / ((64 : ℕ) : ℝ) = -(n : ℝ) * L2 := by
      have h := hsplit
      have hr : (-(n : ℝ)) = 4096 * ((M : ℝ) - 1023) + 64 * (j2 : ℝ) + (j1 : ℝ) := by
        qc h
      rw [hr, L2]; push_cast; ring
    have hprod : 2 ^ M / 2 ^ 1023 * (Real.exp ((j1 : ℝ) * Real.log 2 / ((4096 : ℕ) : ℝ)) *
        Real.exp ((j2 : ℝ) * Real.log 2 / ((64 : ℕ) : ℝ)) * Real.exp Y) =
        Real.exp (fv xh + fv xl) * Real.exp (Y - (fv xh + fv xl + n * L2)) := by
      rw [h2M, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      refine congrArg Real.exp ?_
      linarith [hs]
    rw [hprod]
    have hδ : |Y - (fv xh + fv xl + n * L2)| ≤ 1 / 2 ^ 70 := hY
    have := Real.abs_exp_sub_one_le (x := Y - (fv xh + fv xl + n * L2))
      (hδ.trans (by norm_num))
    rw [show Real.exp (fv xh + fv xl) * Real.exp (Y - (fv xh + fv xl + n * L2)) -
      Real.exp (fv xh + fv xl) = Real.exp (fv xh + fv xl) *
        (Real.exp (Y - (fv xh + fv xl + n * L2)) - 1) by ring, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have : |Real.exp (Y - (fv xh + fv xl + n * L2)) - 1| ≤ 1 / 2 ^ 69 := by
      linarith [show 2 * (1 / 2 ^ 70 : ℝ) = 1 / 2 ^ 69 by norm_num]
    exact (mul_le_mul_of_nonneg_left this (Real.exp_pos _).le).trans (le_of_eq (mul_comm _ _))
  exact final_scale _ _ _ _ _ M p2 hd hdm hMb.1 hMb.2 hV hDV (by
    linarith [(abs_le.mp hxl').1, show (1 : ℝ) / 2 ^ 40 ≤ 1 by norm_num])

#print axioms tab_pr
#print axioms final_scale
#print axioms exp1_err

end Library.Numerics.Float64.Erfc.ErfcExp1
