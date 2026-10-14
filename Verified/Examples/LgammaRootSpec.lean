import Verified.Examples.LgammaRootPath

/-!
**One range of the polynomials about the negative zeros** of `Lgamma.accurate`, from the shifted
argument to the product `z P (2^E z)` (`root_spec`).  The code computes `z = sx + x0` as
`zh + zl` within `|z|/2^71` (`LgammaRootPath.z_spec`), scales it exactly by `2^E`
(`scale_exact`), evaluates the polynomial (`poly_part`), and multiplies by `mulDD`.  With
`RootFact` and `RootMinFact` as hypotheses, `|log |Γ sx|| ≥ 2^-60` and the polynomial within
`2^-63` relative plus `2^-120`, the result lies within `|log |Γ sx||/2^56`, given the range
`[Pmin, Pmax]` of `|P|` on `[-Xn, Xp]`, its Lipschitz constant, and the end bounds of the
kernel check.
-/

namespace Verified.Examples.LgammaRootSpec
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx Tgamma TgammaDD LgammaRootPath

set_option exponentiation.threshold 4096

local notation "tab" => Lgamma.accurateTable
local notation "q" => LgammaApprox.q Lgamma.accurateTable

set_option maxHeartbeats 16000000 in
/-- **One range**: the code's `mulDD zh zl fh fl` within `|log |Γ sx||/2^56` of `log |Γ sx|`. -/
theorem root_spec (hF : FmaSpec.FmaNearest)
    (O N k E p P : ℕ) (hN1 : 1 ≤ N) (hk1 : 1 ≤ k) (hE : E ≤ 30) (hp : p ≤ 10) (hP0 : 0 < P)
    (hon : O + 3 + 2 * N + 2 * k < 2 ^ 63)
    (oU nU kU : UInt64) (hoU : oU.toNat = O) (hnk : (nU - kU).toNat = N) (hkU : kU.toNat = k)
    (h3 : (oU + 3).toNat = O + 3) (h3n : (oU + 3 + 2 * (nU - kU)).toNat = O + 3 + 2 * N)
    (h1 : (oU + 1).toNat = O + 1) (h2 : (oU + 2).toNat = O + 2)
    (sc : Float) (hscf : Finite sc.toBits)
    (hscm : Wasm.IEEE64.scaledMagnitude sc.toBits = 2 ^ (1074 + E))
    (hscv : value sc.toBits = 2 ^ E)
    (hf0 : Wasm.IEEE64.isFinite tab[O]! = true) (hf1 : Wasm.IEEE64.isFinite tab[O + 1]! = true)
    (hf2 : Wasm.IEEE64.isFinite tab[O + 2]! = true)
    -- the kernel checks
    (Xp Xn Xh Xl : ℚ) (C Cl Es Λ K : List ℚ)
    (hok : LgammaRootEval.rootIvOk tab (O + 3) N k P Xp Xn Xh Xl C Cl Es Λ K = true)
    (hE0 : ∀ m, 0 ≤ Es.getD m 0) (hΛ0 : ∀ m, 0 ≤ Λ.getD m 0)
    (Xt Rt Lt : ℚ)
    (htok : TgammaExpr.ok (LgammaRootEval.hornerE tab (O + 3 + 2 * N) k (k - 1)) Xt = true)
    (hLt : TgammaPolyLip.lipQ Rt (0 :: tailList tab (O + 3 + 2 * N) k) ≤ Lt)
    (hXb : Xt * (tM tab (O + 3 + 2 * N) k Xt + tE tab (O + 3 + 2 * N) k Xt) ≤ 1)
    (htop : Xt * (tM tab (O + 3 + 2 * N) k Xt + tE tab (O + 3 + 2 * N) k Xt) * (1 + 1 / 2 ^ 53) +
      1 / 2 ^ 1075 ≤ PolyBound.qabs (PolyBound.ratOfWord tab[O + 3 + 2 * (N - 1)]!))
    (hEi : (Xt * tE tab (O + 3 + 2 * N) k Xt + Xt * (tM tab (O + 3 + 2 * N) k Xt +
        tE tab (O + 3 + 2 * N) k Xt) / 2 ^ 53 + 1 / 2 ^ 1075 + Lt * Xl) +
        (Xt * (tM tab (O + 3 + 2 * N) k Xt + tE tab (O + 3 + 2 * N) k Xt) * (1 + 1 / 2 ^ 53) +
        1 / 2 ^ 1075 + Cl.getD (N - 1) 0) / 2 ^ 53 ≤ Es.getD 0 0)
    (hΛi : (Xt * (tM tab (O + 3 + 2 * N) k Xt + tE tab (O + 3 + 2 * N) k Xt) * (1 + 1 / 2 ^ 53) +
        1 / 2 ^ 1075 + Cl.getD (N - 1) 0) * (1 + 1 / 2 ^ 53) ≤ Λ.getD 0 0)
    (Plo Phi Pmin Pmax : ℚ)
    (hrp : LgammaRootEval.rangeOk (LgammaRootEval.cf tab (O + 3) N) (N + k) P Xp Plo Phi = true)
    (hrn : LgammaRootEval.rangeOk (LgammaRootEval.cfNeg tab (O + 3) N) (N + k) P Xn Plo Phi = true)
    (hPm : 0 < Pmin ∧ ((Pmin ≤ Plo ∧ Phi ≤ Pmax) ∨ (-Pmax ≤ Plo ∧ Phi ≤ -Pmin)))
    (Lp : ℚ) (hLp : TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab (O + 3) N ++
      LgammaApprox.coeffs tab (O + 3 + 2 * N) 2 k) ≤ Lp)
    -- the numeric conditions
    (A B : ℚ) (he0 : 2 ^ p ≤ q O) (he1 : PolyBound.qabs (q (O + 1)) ≤ 2 ^ p / 2 ^ 53)
    (he2 : PolyBound.qabs (q (O + 2)) ≤ 1 / 2 ^ 100) (hB : 2 ^ p ≤ -B) (hA : -A < 2 ^ (p + 1))
    (hnA : -(1 / 2) ≤ q O + A) (hnB : q O + B ≤ 1 / 2)
    (hsA : -Xn + 1 / 2 ^ 40 ≤ 2 ^ E * (A + LgammaApprox.rootX0 O))
    (hsB : 2 ^ E * (B + LgammaApprox.rootX0 O) ≤ Xp - 1 / 2 ^ 40)
    (hX1 : Xp ≤ 1 ∧ Xn ≤ 1 ∧ 0 ≤ Xp ∧ 0 ≤ Xn)
    (hXh : Xp + Xl ≤ Xh ∧ Xn + Xl ≤ Xh) (hXl : 2 ^ E * (1 / 2 ^ 51 + 1 / 2 ^ 99) ≤ Xl)
    (hXt : Xh ≤ Xt ∧ Xh ≤ Rt)
    (hc1 : Pmax ≤ 2 ^ 10 * Pmin) (hc2 : Lp ≤ 2 ^ 10 * Pmin) (hc3 : Es.getD (N - 1) 0 ≤ Pmin / 2 ^ 70)
    (hc4 : Λ.getD (N - 1) 0 ≤ Pmin / 2 ^ 40) (hc5 : Pmax ≤ 2 ^ 19)
    -- the argument and the approximation facts
    (sx : Float) (hsx : Finite sx.toBits) (hvA : (A : ℝ) ≤ value sx.toBits)
    (hvB : value sx.toBits ≤ B)
    (hRF : |GammaBasic.lgamma (value sx.toBits) - (value sx.toBits + LgammaApprox.rootX0 O) *
      LgammaApprox.rootPoly O (N + k) k (2 ^ E * (value sx.toBits + LgammaApprox.rootX0 O))| ≤
        1 / 2 ^ 63 * |GammaBasic.lgamma (value sx.toBits)| + 1 / 2 ^ 120)
    (hRM : 1 / 2 ^ 60 ≤ |GammaBasic.lgamma (value sx.toBits)|)
    -- the code
    (zh zl : Float) (hT : fastTwoSum (entry tab oU + sx) (entry tab (oU + 1)) = (zh, zl))
    (fh fl : Float)
    (hD : Lgamma.polyDD tab (oU + 3) (nU - kU) (zh * sc) ((zl + entry tab (oU + 2)) * sc)
      ((zh * sc) * Lgamma.polyD tab (oU + 3 + 2 * (nU - kU)) kU (zh * sc)) = (fh, fl)) :
    Finite (mulDD zh (zl + entry tab (oU + 2)) fh fl).1.toBits ∧
      Finite (mulDD zh (zl + entry tab (oU + 2)) fh fl).2.toBits ∧
      |value (mulDD zh (zl + entry tab (oU + 2)) fh fl).1.toBits +
          value (mulDD zh (zl + entry tab (oU + 2)) fh fl).2.toBits -
          GammaBasic.lgamma (value sx.toBits)| ≤
        |GammaBasic.lgamma (value sx.toBits)| / 2 ^ 56 := by
  -- the finite pairs of the double-double part
  have hfin : ∀ i < N, Wasm.IEEE64.isFinite tab[O + 3 + 2 * i]! = true ∧
      Wasm.IEEE64.isFinite tab[O + 3 + 2 * i + 1]! = true := by
    simp only [LgammaRootEval.rootIvOk, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      decide_eq_true_eq] at hok
    exact fun i hi => (hok.1.1.1.2 i hi).1.1.1.1
  -- the words of `-x0`
  have e0f := TgammaWords.ofBits_finite _ hf0
  have e1f := TgammaWords.ofBits_finite _ hf1
  have e2f := TgammaWords.ofBits_finite _ hf2
  have ee0 : entry tab oU = Float.ofBits tab[O]! := TgammaPolyDDD.entry_eq _ _ _ hoU
  have ee1 : entry tab (oU + 1) = Float.ofBits tab[O + 1]! := TgammaPolyDDD.entry_eq _ _ _ h1
  have ee2 : entry tab (oU + 2) = Float.ofBits tab[O + 2]! := TgammaPolyDDD.entry_eq _ _ _ h2
  have v0 : value (Float.ofBits tab[O]!).toBits = (q O : ℝ) := TgammaWords.ofBits_value _ hf0
  have v1 : value (Float.ofBits tab[O + 1]!).toBits = (q (O + 1) : ℝ) :=
    TgammaWords.ofBits_value _ hf1
  have v2 : value (Float.ofBits tab[O + 2]!).toBits = (q (O + 2) : ℝ) :=
    TgammaWords.ofBits_value _ hf2
  rw [ee0, ee1] at hT
  rw [ee2] at hD ⊢
  have hX0 : ((LgammaApprox.rootX0 O : ℚ) : ℝ) = (q O : ℝ) + (q (O + 1) : ℝ) + (q (O + 2) : ℝ) := by
    simp only [LgammaApprox.rootX0]; push_cast; ring
  -- the reference
  obtain ⟨L, hL⟩ : ∃ L, L = GammaBasic.lgamma (value sx.toBits) := ⟨_, rfl⟩
  rw [← hL] at hRF hRM ⊢
  obtain ⟨z, hz⟩ : ∃ z, z = value sx.toBits + ((LgammaApprox.rootX0 O : ℚ) : ℝ) := ⟨_, rfl⟩
  rw [← hz] at hRF
  have hzv : z = value sx.toBits + (value (Float.ofBits tab[O]!).toBits +
      value (Float.ofBits tab[O + 1]!).toBits + value (Float.ofBits tab[O + 2]!).toBits) := by
    rw [hz, hX0, v0, v1, v2]
  -- the exact argument `s = 2^E z` and the polynomial there
  have hE2 : (0 : ℝ) < 2 ^ E := by positivity
  have hsA' : -(Xn : ℝ) + 1 / 2 ^ 40 ≤ 2 ^ E * z := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsA
    push_cast at h
    rw [hz]
    nlinarith
  have hsB' : 2 ^ E * z ≤ (Xp : ℝ) - 1 / 2 ^ 40 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hsB
    push_cast at h
    rw [hz]
    nlinarith
  obtain ⟨hX1p, hX1n, hX0p, hX0n⟩ := hX1
  have hX1p' : (Xp : ℝ) ≤ 1 := by exact_mod_cast hX1p
  have hX1n' : (Xn : ℝ) ≤ 1 := by exact_mod_cast hX1n
  have hs1 : |2 ^ E * z| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hPeq : ∀ t : ℝ, LgammaApprox.rootPoly O (N + k) k t =
      TgammaPoly.horner (fun j => (LgammaRootEval.cf tab (O + 3) N j : ℝ)) (N + k) 0 t
        (N + k - 1) := by
    intro t
    rw [LgammaRootEval.horner_cf_eval tab (O + 3) N k (by omega) hfin t, LgammaApprox.rootPoly,
      show N + k - k = N by omega]
  obtain ⟨hPlo, hPhi⟩ := LgammaRootEval.root_range tab (O + 3) N k P Xp Xn Plo Phi hP0 (by omega)
    hrp hrn (2 ^ E * z) (by linarith) (by linarith)
  rw [← hPeq] at hPlo hPhi
  set Ps := LgammaApprox.rootPoly O (N + k) k (2 ^ E * z) with hPs
  obtain ⟨hPmin0, hPm'⟩ := hPm
  have hPmin0' : (0 : ℝ) < Pmin := by exact_mod_cast hPmin0
  have hPsb : (Pmin : ℝ) ≤ |Ps| ∧ |Ps| ≤ Pmax := by
    rcases hPm' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · have ha' : (Pmin : ℝ) ≤ Plo := by exact_mod_cast ha
      have hb' : (Phi : ℝ) ≤ Pmax := by exact_mod_cast hb
      rw [abs_of_pos (by linarith)]
      exact ⟨by linarith, by linarith⟩
    · have ha' : -(Pmax : ℝ) ≤ Plo := by exact_mod_cast ha
      have hb' : (Phi : ℝ) ≤ -Pmin := by exact_mod_cast hb
      rw [abs_of_neg (by linarith)]
      exact ⟨by linarith, by linarith⟩
  have hc5' : (Pmax : ℝ) ≤ 2 ^ 19 := by exact_mod_cast hc5
  have hc1' : (Pmax : ℝ) ≤ 2 ^ 10 * Pmin := by exact_mod_cast hc1
  -- `|z|` from below and above
  have hzP : |z * Ps| = |z| * |Ps| := abs_mul _ _
  have hLz : |L| ≤ |z| * |Ps| + 1 / 2 ^ 63 * |L| + 1 / 2 ^ 120 := by
    have := abs_sub_abs_le_abs_sub L (z * Ps)
    linarith
  have hzL : |z| * |Ps| ≤ |L| + 1 / 2 ^ 63 * |L| + 1 / 2 ^ 120 := by
    have := abs_sub_abs_le_abs_sub (z * Ps) L
    rw [abs_sub_comm] at this
    linarith
  have hz80 : 1 / 2 ^ 80 ≤ |z| := by
    by_contra hc
    push Not at hc
    have : |z| * |Ps| ≤ 1 / 2 ^ 80 * 2 ^ 19 :=
      mul_le_mul hc.le (hPsb.2.trans hc5') (abs_nonneg _) (by positivity)
    nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 80 * 2 ^ 19 < 1 / 2 ^ 60 * (1 - 1 / 2 ^ 63) - 1 / 2 ^ 120)]
  have hzup : |z| * Pmin ≤ |L| * (1 + 1 / 2 ^ 59) := by
    have := mul_le_mul_of_nonneg_left hPsb.1 (abs_nonneg z)
    nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 120 ≤ 1 / 2 ^ 60 * (1 / 2 ^ 60))]
  -- the shifted argument
  have hv1 : (2 : ℝ) ^ p ≤ -value sx.toBits := by
    have h := (Rat.cast_le (K := ℝ)).mpr hB; push_cast at h; linarith
  have hv2 : -value sx.toBits < 2 ^ (p + 1) := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hA; push_cast at h; linarith
  have hnear : |value (Float.ofBits tab[O]!).toBits + value sx.toBits| ≤ 1 / 2 := by
    rw [v0]
    have hA' := (Rat.cast_le (K := ℝ)).mpr hnA
    have hB' := (Rat.cast_le (K := ℝ)).mpr hnB
    push_cast at hA' hB'
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have he0' : (2 : ℝ) ^ p ≤ value (Float.ofBits tab[O]!).toBits := by
    rw [v0]; exact_mod_cast he0
  have he1' : |value (Float.ofBits tab[O + 1]!).toBits| ≤ 2 ^ p / 2 ^ 53 := by
    rw [v1, ← TgammaExpr.qabs_cast]
    have h := (Rat.cast_le (K := ℝ)).mpr he1; push_cast at h ⊢; linarith
  have he2' : |value (Float.ofBits tab[O + 2]!).toBits| ≤ 1 / 2 ^ 100 := by
    rw [v2, ← TgammaExpr.qabs_cast]
    have h := (Rat.cast_le (K := ℝ)).mpr he2; push_cast at h ⊢; linarith
  obtain ⟨zf, z2f, hze, hzl2, hzh1⟩ := z_spec _ _ _ sx e0f e1f e2f hsx p hp he0' hv1 hv2 hnear he1'
    he2' (by rw [← hzv]; exact hz80) zh zl hT
  rw [← hzv] at hze
  set zl2 := zl + Float.ofBits tab[O + 2]! with hzl2def
  have hzl2b : |value zl2.toBits| ≤ 1 / 2 ^ 51 + 1 / 2 ^ 99 := by
    linarith [div_le_div_of_nonneg_right hzh1 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)]
  -- the exact scalings
  obtain ⟨shf, shv⟩ := scale_exact zh sc zf hscf E hE hscm (by linarith)
  obtain ⟨slf, slv⟩ := scale_exact zl2 sc z2f hscf E hE hscm
    (by linarith [(by norm_num : (1 : ℝ) / 2 ^ 51 + 1 / 2 ^ 99 < 2)])
  rw [hscv] at shv slv
  have hsc_eq : value (zh * sc).toBits + value (zl2 * sc).toBits =
      2 ^ E * (value zh.toBits + value zl2.toBits) := by rw [shv, slv]; ring
  have hsd : |value (zh * sc).toBits + value (zl2 * sc).toBits - 2 ^ E * z| ≤ 1 / 2 ^ 71 := by
    rw [hsc_eq, ← mul_sub, abs_mul, abs_of_pos hE2]
    have := mul_le_mul_of_nonneg_left hze hE2.le
    have h2 : 2 ^ E * (|z| / 2 ^ 71) = |2 ^ E * z| / 2 ^ 71 := by
      rw [abs_mul, abs_of_pos hE2]; ring
    linarith [div_le_div_of_nonneg_right hs1 (by norm_num : (0 : ℝ) ≤ 2 ^ 71)]
  have hs1c : -(Xn : ℝ) ≤ value (zh * sc).toBits + value (zl2 * sc).toBits := by
    linarith [(abs_le.mp hsd).1, (by norm_num : (1 : ℝ) / 2 ^ 71 ≤ 1 / 2 ^ 40)]
  have hs2c : value (zh * sc).toBits + value (zl2 * sc).toBits ≤ Xp := by
    linarith [(abs_le.mp hsd).2, (by norm_num : (1 : ℝ) / 2 ^ 71 ≤ 1 / 2 ^ 40)]
  have hXl' : |value (zl2 * sc).toBits| ≤ (Xl : ℝ) := by
    have h := (Rat.cast_le (K := ℝ)).mpr hXl
    push_cast at h
    rw [slv, abs_mul, abs_of_pos hE2]
    nlinarith [abs_nonneg (value zl2.toBits)]
  obtain ⟨hXhp, hXhn⟩ := hXh
  have hXhp' : (Xp : ℝ) + Xl ≤ Xh := by exact_mod_cast hXhp
  have hXhn' : (Xn : ℝ) + Xl ≤ Xh := by exact_mod_cast hXhn
  have hscb : |value (zh * sc).toBits + value (zl2 * sc).toBits| ≤ (Xh : ℝ) - Xl := by
    rw [abs_le]; constructor <;> linarith
  have hXh' : |value (zh * sc).toBits| ≤ (Xh : ℝ) := by
    have := abs_sub_abs_le_abs_sub (value (zh * sc).toBits)
      (value (zh * sc).toBits + value (zl2 * sc).toBits)
    rw [show value (zh * sc).toBits - (value (zh * sc).toBits + value (zl2 * sc).toBits) =
      -value (zl2 * sc).toBits by ring, abs_neg] at this
    linarith
  obtain ⟨hXt1, hRt1⟩ := hXt
  have hXt1' : (Xh : ℝ) ≤ Xt := by exact_mod_cast hXt1
  have hRt1' : (Xh : ℝ) ≤ Rt := by exact_mod_cast hRt1
  have hXl0 : (0 : ℝ) ≤ Xl := (abs_nonneg _).trans hXl'
  -- the polynomial
  obtain ⟨fhf, flf, hfe, hfl⟩ := poly_part hF tab (O + 3) N k P hN1 hk1 (by omega) (oU + 3)
    (nU - kU) (oU + 3 + 2 * (nU - kU)) kU h3 hnk h3n hkU Xp Xn Xh Xl C Cl Es Λ K hok hE0 hΛ0 Xt Rt Lt
    htok hLt hXb htop hEi hΛi (zh * sc) (zl2 * sc) shf slf hXh' hXl' (hXh'.trans hXt1')
    (hXh'.trans hRt1') (by linarith) hs1c hs2c fh fl hD
  rw [show N - 1 + k = N + k - 1 by omega, ← hPeq] at hfe
  set sc' := value (zh * sc).toBits + value (zl2 * sc).toBits with hsc'
  set Pc := LgammaApprox.rootPoly O (N + k) k sc' with hPc
  -- the Lipschitz step
  have hlip : |Pc - Ps| ≤ (Lp : ℝ) * (1 / 2 ^ 71) := by
    have h := TgammaPolyLip.eval_lip 1 (by norm_num) sc' (2 ^ E * z)
      (by push_cast; rw [abs_le]; constructor <;> linarith) (by push_cast; exact hs1)
      (LgammaApprox.ddCoeffs tab (O + 3) N ++ LgammaApprox.coeffs tab (O + 3 + 2 * N) 2 k)
    have hLp' : ((TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab (O + 3) N ++
        LgammaApprox.coeffs tab (O + 3 + 2 * N) 2 k) : ℚ) : ℝ) ≤ Lp := by exact_mod_cast hLp
    have hL0 : (0 : ℝ) ≤ ((TgammaPolyLip.lipQ 1 (LgammaApprox.ddCoeffs tab (O + 3) N ++
        LgammaApprox.coeffs tab (O + 3 + 2 * N) 2 k) : ℚ) : ℝ) := by
      exact_mod_cast TgammaPolyLip.lipQ_nonneg 1 (by norm_num) _
    have e1 : Pc = PolyBound.eval (LgammaApprox.ddCoeffs tab (O + 3) N ++
        LgammaApprox.coeffs tab (O + 3 + 2 * N) 2 k) sc' := by
      rw [hPc, LgammaApprox.rootPoly, show N + k - k = N by omega]
    have e2 : Ps = PolyBound.eval (LgammaApprox.ddCoeffs tab (O + 3) N ++
        LgammaApprox.coeffs tab (O + 3 + 2 * N) 2 k) (2 ^ E * z) := by
      rw [hPs, LgammaApprox.rootPoly, show N + k - k = N by omega]
    rw [e1, e2]
    calc _ ≤ _ := h
      _ ≤ (Lp : ℝ) * (1 / 2 ^ 71) := mul_le_mul hLp' hsd (abs_nonneg _) (hL0.trans hLp')
  -- magnitudes
  have hc2' : (Lp : ℝ) ≤ 2 ^ 10 * Pmin := by exact_mod_cast hc2
  have hc3' : (Es.getD (N - 1) 0 : ℝ) ≤ Pmin / 2 ^ 70 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hc3; push_cast at h; exact h
  have hc4' : (Λ.getD (N - 1) 0 : ℝ) ≤ Pmin / 2 ^ 40 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hc4; push_cast at h; exact h
  have hΛe0 : (0 : ℝ) ≤ Λ.getD (N - 1) 0 := (abs_nonneg _).trans hfl
  have hPmm : (Pmin : ℝ) ≤ Pmax := hPsb.1.trans hPsb.2
  have hz1 : |z| ≤ 1 := by
    have h1 : (1 : ℝ) ≤ 2 ^ E := one_le_pow₀ (by norm_num)
    rw [abs_mul, abs_of_pos hE2] at hs1
    nlinarith [abs_nonneg z]
  have hZc : |value zh.toBits + value zl2.toBits| ≤ |z| * (1 + 1 / 2 ^ 71) := by
    have := abs_sub_abs_le_abs_sub (value zh.toBits + value zl2.toBits) z
    linarith
  have h19 : (1 : ℝ) / 2 ^ 99 ≤ |z| / 2 ^ 19 := by
    have := div_le_div_of_nonneg_right hz80 (by norm_num : (0 : ℝ) ≤ 2 ^ 19)
    linarith [(by norm_num : (1 : ℝ) / 2 ^ 99 = 1 / 2 ^ 80 / 2 ^ 19)]
  have hzh2 : |value zh.toBits| ≤ 2 * |z| := by
    have := abs_sub_abs_le_abs_sub (value zh.toBits) (-value zl2.toBits)
    rw [sub_neg_eq_add, abs_neg] at this
    nlinarith [abs_nonneg z, abs_nonneg (value zh.toBits)]
  have hzl2' : |value zl2.toBits| ≤ |z| / 2 ^ 18 := by
    have := div_le_div_of_nonneg_right hzh2 (by norm_num : (0 : ℝ) ≤ 2 ^ 51)
    nlinarith [abs_nonneg z]
  have hPc : |Pc| ≤ Pmax + Lp / 2 ^ 71 := by
    have := abs_sub_abs_le_abs_sub Pc Ps
    linarith [hPsb.2]
  have hfh : |value fh.toBits| ≤ 2 * Pmax := by
    have h1 := abs_sub_abs_le_abs_sub (value fh.toBits + value fl.toBits) Pc
    have h2 := abs_sub_abs_le_abs_sub (value fh.toBits) (-value fl.toBits)
    rw [sub_neg_eq_add, abs_neg] at h2
    have : (Lp : ℝ) / 2 ^ 71 ≤ Pmax / 2 ^ 61 := by
      have := div_le_div_of_nonneg_right (hc2'.trans (by nlinarith : (2 : ℝ) ^ 10 * Pmin ≤
        2 ^ 10 * Pmax)) (by norm_num : (0 : ℝ) ≤ 2 ^ 71)
      linarith
    nlinarith
  -- the product
  have hW0 : (0 : ℝ) ≤ |z| * Pmin := by positivity
  obtain ⟨mf1, mf2, me, -, -⟩ := TgammaMul.mulDD_spec hF zh zl2 fh fl zf z2f fhf flf
    (4 * Pmax * |z|) (2 * Pmax * (|z| / 2 ^ 18)) (Λ.getD (N - 1) 0 * (2 * |z|))
    (Λ.getD (N - 1) 0 * (|z| / 2 ^ 18))
    (by rw [show 4 * (Pmax : ℝ) * |z| = (2 * Pmax) * (2 * |z|) by ring]
        exact mul_le_mul hfh hzh2 (abs_nonneg _) (by linarith [abs_nonneg (value fh.toBits)]))
    (mul_le_mul hfh hzl2' (abs_nonneg _) (by linarith [abs_nonneg (value fh.toBits)]))
    (mul_le_mul hfl hzh2 (abs_nonneg _) hΛe0)
    (mul_le_mul hfl hzl2' (abs_nonneg _) hΛe0)
    (by nlinarith [abs_nonneg z, (by norm_num : (4 : ℝ) * 2 ^ 19 ≤ 2 ^ 900)])
    (by nlinarith [abs_nonneg z, (by norm_num : (2 : ℝ) * 2 ^ 19 + 2 ^ 19 ≤ 2 ^ 900)])
  refine ⟨mf1, mf2, ?_⟩
  -- the error
  set r1 := value (mulDD zh zl2 fh fl).1.toBits
  set r2 := value (mulDD zh zl2 fh fl).2.toBits
  have k : r1 + r2 - L = (r1 + r2 - (value zh.toBits + value zl2.toBits) *
        (value fh.toBits + value fl.toBits)) +
      (value zh.toBits + value zl2.toBits) * (value fh.toBits + value fl.toBits - Pc) +
      (value zh.toBits + value zl2.toBits) * (Pc - Ps) +
      (value zh.toBits + value zl2.toBits - z) * Ps + (z * Ps - L) := by ring
  rw [k]
  have t1 : |(value zh.toBits + value zl2.toBits) * (value fh.toBits + value fl.toBits - Pc)| ≤
      |z| * Pmin * ((1 + 1 / 2 ^ 71) / 2 ^ 70) := by
    rw [abs_mul]
    have := mul_le_mul hZc (hfe.trans hc3') (abs_nonneg _) (by positivity)
    linarith
  have t2 : |(value zh.toBits + value zl2.toBits) * (Pc - Ps)| ≤
      |z| * Pmin * ((1 + 1 / 2 ^ 71) * 2 ^ 10 / 2 ^ 71) := by
    rw [abs_mul]
    have h1 := mul_le_mul hZc hlip (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hc2' (by positivity : (0 : ℝ) ≤ |z| * (1 + 1 / 2 ^ 71))
    nlinarith
  have t3 : |(value zh.toBits + value zl2.toBits - z) * Ps| ≤ |z| * Pmin * (2 ^ 10 / 2 ^ 71) := by
    rw [abs_mul]
    have h1 := mul_le_mul hze hPsb.2 (abs_nonneg _) (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hc1' (by positivity : (0 : ℝ) ≤ |z| / 2 ^ 71)
    nlinarith
  have t4 : |z * Ps - L| ≤ 1 / 2 ^ 63 * |L| + 1 / 2 ^ 120 := by rw [abs_sub_comm]; exact hRF
  have t5 : |r1 + r2 - (value zh.toBits + value zl2.toBits) * (value fh.toBits + value fl.toBits)| ≤
      |z| * Pmin * (2 ^ 13 / 2 ^ 71 + 1 / 2 ^ 58 + 8 / 2 ^ 93 + 2 ^ 12 / 2 ^ 104) + 1 / 2 ^ 1070 := by
    have h1 := mul_le_mul_of_nonneg_right hc1' (by positivity : (0 : ℝ) ≤ |z|)
    have h2 := mul_le_mul_of_nonneg_right hc4' (by positivity : (0 : ℝ) ≤ |z|)
    nlinarith
  have hfin : |L| * (1 + 1 / 2 ^ 59) * (2 ^ 13 / 2 ^ 71 + 1 / 2 ^ 58 + 8 / 2 ^ 93 + 2 ^ 12 / 2 ^ 104 +
      (1 + 1 / 2 ^ 71) / 2 ^ 70 + (1 + 1 / 2 ^ 71) * 2 ^ 10 / 2 ^ 71 + 2 ^ 10 / 2 ^ 71) + 1 / 2 ^ 1070 +
      1 / 2 ^ 63 * |L| + 1 / 2 ^ 120 ≤ |L| / 2 ^ 56 := by
    have hL0 := abs_nonneg L
    nlinarith [(by norm_num : (1 : ℝ) / 2 ^ 1070 ≤ 1 / 2 ^ 60 * (1 / 2 ^ 1000)),
      (by norm_num : (1 : ℝ) / 2 ^ 120 ≤ 1 / 2 ^ 60 * (1 / 2 ^ 60)),
      (by norm_num : ((1 : ℝ) + 1 / 2 ^ 59) * (2 ^ 13 / 2 ^ 71 + 1 / 2 ^ 58 + 8 / 2 ^ 93 + 2 ^ 12 / 2 ^ 104 +
        (1 + 1 / 2 ^ 71) / 2 ^ 70 + (1 + 1 / 2 ^ 71) * 2 ^ 10 / 2 ^ 71 + 2 ^ 10 / 2 ^ 71) +
        1 / 2 ^ 1000 + 1 / 2 ^ 63 + 1 / 2 ^ 60 ≤ 1 / 2 ^ 56)]
  have hWL : |z| * Pmin * (2 ^ 13 / 2 ^ 71 + 1 / 2 ^ 58 + 8 / 2 ^ 93 + 2 ^ 12 / 2 ^ 104 +
      (1 + 1 / 2 ^ 71) / 2 ^ 70 + (1 + 1 / 2 ^ 71) * 2 ^ 10 / 2 ^ 71 + 2 ^ 10 / 2 ^ 71) ≤
      |L| * (1 + 1 / 2 ^ 59) * (2 ^ 13 / 2 ^ 71 + 1 / 2 ^ 58 + 8 / 2 ^ 93 + 2 ^ 12 / 2 ^ 104 +
      (1 + 1 / 2 ^ 71) / 2 ^ 70 + (1 + 1 / 2 ^ 71) * 2 ^ 10 / 2 ^ 71 + 2 ^ 10 / 2 ^ 71) :=
    mul_le_mul_of_nonneg_right hzup (by positivity)
  have e1 := abs_add_le ((r1 + r2 - (value zh.toBits + value zl2.toBits) *
        (value fh.toBits + value fl.toBits)) +
      (value zh.toBits + value zl2.toBits) * (value fh.toBits + value fl.toBits - Pc) +
      (value zh.toBits + value zl2.toBits) * (Pc - Ps) +
      (value zh.toBits + value zl2.toBits - z) * Ps) (z * Ps - L)
  have e2 := abs_add_le ((r1 + r2 - (value zh.toBits + value zl2.toBits) *
        (value fh.toBits + value fl.toBits)) +
      (value zh.toBits + value zl2.toBits) * (value fh.toBits + value fl.toBits - Pc) +
      (value zh.toBits + value zl2.toBits) * (Pc - Ps)) ((value zh.toBits + value zl2.toBits - z) * Ps)
  have e3 := abs_add_le ((r1 + r2 - (value zh.toBits + value zl2.toBits) *
        (value fh.toBits + value fl.toBits)) +
      (value zh.toBits + value zl2.toBits) * (value fh.toBits + value fl.toBits - Pc))
      ((value zh.toBits + value zl2.toBits) * (Pc - Ps))
  have e4 := abs_add_le (r1 + r2 - (value zh.toBits + value zl2.toBits) *
        (value fh.toBits + value fl.toBits))
      ((value zh.toBits + value zl2.toBits) * (value fh.toBits + value fl.toBits - Pc))
  linarith

#print axioms root_spec

end Verified.Examples.LgammaRootSpec
