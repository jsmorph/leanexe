import Library.Numerics.Float64.Bessel.BesselMillerLast
import Library.Numerics.Float64.Bessel.BesselJ0Small
import Library.Numerics.Float64.Bessel.BesselJ1Small

/-!
Miller's method of `jn` for `2^-30 ≤ x < 2` and `2 ≤ n ≤ 2^31`: the result is finite and lies
within `(23 + 8 n) u J_n(x) + 2^-1060` of `J_n(x)` (`jn_backward`).  `backward_eq` writes
`Bessel.jnBackward` as the continued fraction (`BesselMillerDepth.cf_depth`,
`BesselMillerT.t_value`), the flag of the rescaling (`BesselMillerLog.flag_log` and `flag_bound` for
`n ≥ 12`, `small_flag` below), the backward loop (`BesselMillerLast`), and the normalization
`bfinal`.  The normalization divides `t ≈ σ J_n` times `j0 x` by `b ≈ σ J₀` when
`|j0 x| ≥ |j1 x|`, and times `j1 x` by `a ≈ σ J₁` otherwise.  In the first case `J₁ ≤ J₀ + 2^-40`,
so `J₂ ≤ (21/20) J₀` (`BesselMillerFacts.d_one`) and `J₀ ≥ 2/5 - 7 u`; in the second `x > 1`, so
`J₁ ≥ 2/5` (`BesselModulus.J1_mid`).  `final_float` adds the relative errors of `t`, of `j0 x` or
`j1 x`, of `b` or `a`, and two roundings.
-/

namespace Library.Numerics.Float64.Bessel.BesselMillerFinal
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselOrderN BesselRecur
  BesselStepF BesselJnTiny BesselSmallSigns BesselMillerReal BesselMillerCF BesselMillerDepth
  BesselMillerFacts BesselMillerStep BesselMillerT BesselMillerLog BesselMillerBack BesselMillerLast
open LeanExe.ProofKit.Bessel

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The depth of the continued fraction. -/
def kOf (n : UInt64) (xa : Float) : UInt64 :=
  (LeanExe.repeatWhile 0xFFFFFFFF (cinit ((n + n).toFloat / xa) (2.0 / xa)) ccond
    (cstep (2.0 / xa))).2.2.2

/-- The value of the continued fraction. -/
def tinit (n : UInt64) (xa : Float) : Float :=
  LeanExe.loop (kOf n xa + 1) (0.0 : Float) (fbody n (kOf n xa) xa)

/-- The flag of the rescaling. -/
def scaleOf (n : UInt64) (xa : Float) : Bool :=
  !(n.toFloat * Log.logWith Log.logTable Log.logTable2 ((2.0 / xa) * n.toFloat).abs <
    Float.ofBits 0x40862E42FEFA39EF)

/-- The normalization by `j0 x` or `j1 x`. -/
def bfinal (s : Float × Float × Float × Float) (xa : Float) : Float :=
  if (Bessel.j0 xa).abs ≥ (Bessel.j1 xa).abs then s.2.2.1 * Bessel.j0 xa / s.2.1
  else s.2.2.1 * Bessel.j1 xa / s.1

/-- The code of `jnBackward` in terms of the named loops.  The proof extracts the `let`s above
the two matches on loop results and splits the matches; reducing them by `rfl` or by `dsimp`
exceeded the kernel's recursion depth. -/
theorem backward_eq (n : UInt64) (xa : Float) :
    Bessel.jnBackward Trig.invPi Trig.halfPi Log.logTable Log.logTable2 Bessel.j0Table
        Bessel.j1Table n xa =
      bfinal (LeanExe.loop (n - 1) (tinit n xa, 1.0, tinit n xa, (2 * (n - 1)).toFloat)
        (fun _ s => bbody (scaleOf n xa) xa s)) xa := by
  unfold Bessel.jnBackward
  extract_lets (config := { onlyGivenNames := true, underBinder := false }) w h
  split
  rename_i q0 q1 z k heq
  extract_lets (config := { onlyGivenNames := true, underBinder := false }) t tmp scale
  have hk : LeanExe.repeatWhile 0xFFFFFFFF (cinit ((n + n).toFloat / xa) (2.0 / xa)) ccond
      (cstep (2.0 / xa)) = (q0, q1, z, k) := heq
  have hkOf : kOf n xa = k := by
    unfold kOf
    rw [hk]
  unfold tinit
  rw [hkOf]
  split
  rename_i a b t' d heq2
  have hl : LeanExe.loop (n - 1) (LeanExe.loop (k + 1) (0.0 : Float) (fbody n k xa), 1.0,
      LeanExe.loop (k + 1) (0.0 : Float) (fbody n k xa), (2 * (n - 1)).toFloat)
      (fun _ s => bbody (scaleOf n xa) xa s) = (a, b, t', d) := heq2
  rw [hl]
  rfl

theorem fle_iff (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) :
    a ≤ b ↔ value a.toBits ≤ value b.toBits := by
  rw [F64Bits.le_iff]
  unfold Wasm.IEEE64.le
  rw [not_nan_of_finite ha, not_nan_of_finite hb, Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled,
    Library.Numerics.Float64.Trig.TrigSmall.value_of_scaled]
  simp only [Bool.or_false, Bool.false_eq_true, ite_false, decide_eq_true_eq]
  constructor
  · intro h
    exact div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)
  · intro h
    have := (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < 2 ^ 1074)).mp h
    exact_mod_cast this

/-- Without the flag, `1/J_(n-1) ≤ 2^1017` for `n ≤ 11`. -/
theorem small_flag (w : ℝ) (hw : 1 / 2 ^ 30 ≤ w) (hw2 : w < 2) (n : ℕ) (hn : 2 ≤ n)
    (hn11 : n ≤ 11) : 1 / Jn (n - 1) w ≤ 2 ^ 1017 := by
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hg := Jn_ge (n - 1) (by omega) w hw0.le hw2.le
  have hJ := Jn_pos (n - 1) w hw0 hw2.le
  have h1 : (1 / 2 ^ 31 : ℝ) ^ 10 ≤ (w / 2) ^ (n - 1) := by
    calc (1 / 2 ^ 31 : ℝ) ^ 10 ≤ (1 / 2 ^ 31) ^ (n - 1) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ ≤ (w / 2) ^ (n - 1) := pow_le_pow_left₀ (by norm_num) (by linarith) _
  have h2 : ((n - 1).factorial : ℝ) ≤ (10 : ℕ).factorial := by
    exact_mod_cast Nat.factorial_le (by omega)
  have h3 : ((10 : ℕ).factorial : ℝ) = 3628800 := by norm_num [Nat.factorial]
  have hf : (0 : ℝ) < (n - 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have h4 : (1 / 2 ^ 31 : ℝ) ^ 10 / (3 * 3628800) ≤ Jn (n - 1) w := by
    refine le_trans ?_ hg
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    rw [h3] at h2
    nlinarith
  rw [div_le_iff₀ hJ]
  linarith

/-- The flag `scale = false` bounds `1/J_(n-1)`. -/
theorem flag_jn (xa : Float) (n : UInt64) (hxf : Finite xa.toBits)
    (hw : 1 / 2 ^ 30 ≤ value xa.toBits) (hw2 : value xa.toBits < 2) (hn : 2 ≤ n.toNat)
    (hn2 : n.toNat ≤ 2 ^ 31) :
    scaleOf n xa = false → 1 / Jn (n.toNat - 1) (value xa.toBits) ≤ 2 ^ 1017 := by
  intro hs
  have hlt : n.toFloat * Log.logWith Log.logTable Log.logTable2 ((2.0 / xa) * n.toFloat).abs <
      Float.ofBits 0x40862E42FEFA39EF := by
    unfold scaleOf at hs
    simpa using hs
  have hw0 : 0 < value xa.toBits := lt_of_lt_of_le (by norm_num) hw
  by_cases h12 : 12 ≤ n.toNat
  · exact flag_bound _ hw0 hw2 n.toNat h12 (flag_log xa n hxf hw hw2 hn hn2 hlt)
  · exact small_flag _ hw hw2 n.toNat hn (by omega)

/-- The product `t z` relative to `S X Z`. -/
theorem prod_rel {vt vz vp S X Z Et Ez : ℝ} (hS : 0 < S) (hX0 : 0 ≤ X) (hZ : 0 < Z) (hZ3 : Z ≤ 3)
    (hEt0 : 0 ≤ Et) (hEt : Et ≤ 1 / 2 ^ 17) (hEz0 : 0 ≤ Ez) (hEz : Ez ≤ 1 / 2 ^ 17)
    (ht : |vt - S * X| ≤ Et * (S * X) + 1 / 2 ^ 1074) (hz : |vz - Z| ≤ Ez * Z)
    (hp : |vp - vt * vz| ≤ |vt * vz| / 2 ^ 53 + 1 / 2 ^ 1075) :
    |vp - S * X * Z| ≤ ((Et + Ez + Et * Ez) + (1 + 1 / 2 ^ 15) / 2 ^ 53) * (S * X * Z) +
      1 / 2 ^ 1071 := by
  have hP0 : 0 ≤ S * X * Z := by positivity
  have hvz : |vz| ≤ (1 + Ez) * Z := by
    have := abs_sub_abs_le_abs_sub vz Z
    rw [abs_of_pos hZ] at this
    linarith
  have a1 : |(vt - S * X) * vz| ≤ (Et * (S * X) + 1 / 2 ^ 1074) * ((1 + Ez) * Z) := by
    rw [abs_mul]
    exact mul_le_mul ht hvz (abs_nonneg _) (by positivity)
  have a2 : |S * X * (vz - Z)| ≤ S * X * (Ez * Z) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ S * X)]
    exact mul_le_mul_of_nonneg_left hz (by positivity)
  have h1 : |vt * vz - S * X * Z| ≤
      (Et * (S * X) + 1 / 2 ^ 1074) * ((1 + Ez) * Z) + S * X * (Ez * Z) := by
    have e : vt * vz - S * X * Z = (vt - S * X) * vz + S * X * (vz - Z) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add a1 a2)
  have hD : 1 / 2 ^ 1074 * ((1 + Ez) * Z) ≤ 1 / 2 ^ 1072 := by
    have : (1 + Ez) * Z ≤ 4 := by
      have := mul_le_mul hEz hZ3 hZ.le (by norm_num)
      linarith
    calc 1 / 2 ^ 1074 * ((1 + Ez) * Z) ≤ 1 / 2 ^ 1074 * 4 :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 1 / 2 ^ 1072 := by norm_num
  have h1' : |vt * vz - S * X * Z| ≤ (Et + Ez + Et * Ez) * (S * X * Z) + 1 / 2 ^ 1072 := by
    have e : (Et * (S * X) + 1 / 2 ^ 1074) * ((1 + Ez) * Z) + S * X * (Ez * Z) =
        (Et + Ez + Et * Ez) * (S * X * Z) + 1 / 2 ^ 1074 * ((1 + Ez) * Z) := by ring
    rw [e] at h1
    linarith
  have hE1 : Et + Ez + Et * Ez ≤ 1 / 2 ^ 15 := by
    have := mul_le_mul hEt hEz hEz0 (by norm_num)
    linarith
  have hpm : |vt * vz| ≤ (1 + 1 / 2 ^ 15) * (S * X * Z) + 1 / 2 ^ 1072 := by
    have := abs_sub_abs_le_abs_sub (vt * vz) (S * X * Z)
    rw [abs_of_nonneg hP0] at this
    linarith [mul_le_mul_of_nonneg_right hE1 hP0]
  have hdiv : |vt * vz| / 2 ^ 53 ≤ ((1 + 1 / 2 ^ 15) * (S * X * Z) + 1 / 2 ^ 1072) / 2 ^ 53 :=
    div_le_div_of_nonneg_right hpm (by positivity)
  have e : ((1 + 1 / 2 ^ 15) * (S * X * Z) + 1 / 2 ^ 1072) / 2 ^ 53 =
      (1 + 1 / 2 ^ 15) / 2 ^ 53 * (S * X * Z) + 1 / 2 ^ 1125 := by ring
  have := abs_sub_le vp (vt * vz) (S * X * Z)
  linarith

/-- The quotient `p/b` relative to `X`. -/
theorem quot_rel {vp vb vq S X Z Eb E2 : ℝ} (hS : 0 < S) (hX0 : 0 ≤ X) (hZ : 0 < Z)
    (hSZ : 1 / 200 ≤ S * Z) (hEb0 : 0 ≤ Eb) (hEb : Eb ≤ 1 / 2 ^ 17) (hE20 : 0 ≤ E2)
    (hP : |vp - S * X * Z| ≤ E2 * (S * X * Z) + 1 / 2 ^ 1071) (hb : |vb - S * Z| ≤ Eb * (S * Z))
    (hq : |vq - vp / vb| ≤ |vp / vb| / 2 ^ 53 + 1 / 2 ^ 1075) :
    |vq - X| ≤ ((E2 + Eb) * (1 + 1 / 2 ^ 16) + (1 + (E2 + Eb) * (1 + 1 / 2 ^ 16)) / 2 ^ 53) * X +
      1 / 2 ^ 1062 := by
  have hB : 0 < S * Z := by positivity
  have hvb : (1 - Eb) * (S * Z) ≤ vb := by
    have := (abs_le.mp hb).1
    linarith
  have hvb0 : 0 < vb := lt_of_lt_of_le (mul_pos (by linarith) hB) hvb
  obtain ⟨e3, he3⟩ : ∃ e, e = (E2 + Eb) * (1 + 1 / 2 ^ 16) := ⟨_, rfl⟩
  have he30 : 0 ≤ e3 := by rw [he3]; positivity
  have hnum : |(vp - S * X * Z) - X * (vb - S * Z)| ≤ (E2 + Eb) * (S * X * Z) + 1 / 2 ^ 1071 := by
    have h1 := abs_add_le (vp - S * X * Z) (-(X * (vb - S * Z)))
    rw [abs_neg, ← sub_eq_add_neg] at h1
    have h2 : |X * (vb - S * Z)| ≤ X * (Eb * (S * Z)) := by
      rw [abs_mul, abs_of_nonneg hX0]
      exact mul_le_mul_of_nonneg_left hb hX0
    linarith
  have hk1 : 0 ≤ (1 + 1 / 2 ^ 16) * (1 - Eb) - 1 := by linarith
  have hk2 : 1 / 2 ^ 1071 ≤ 1 / 2 ^ 1063 * ((1 - Eb) * (S * Z)) := by
    have : (1 - 1 / 2 ^ 17) * (1 / 200) ≤ (1 - Eb) * (S * Z) :=
      mul_le_mul (by linarith) hSZ (by norm_num) (by linarith)
    have h3 : (1 : ℝ) / 2 ^ 1071 ≤ 1 / 2 ^ 1063 * ((1 - 1 / 2 ^ 17) * (1 / 200)) := by norm_num
    linarith [mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 / 2 ^ 1063)]
  have hP0 : 0 ≤ (E2 + Eb) * (S * X * Z) := by positivity
  have h3 : |vp / vb - X| ≤ e3 * X + 1 / 2 ^ 1063 := by
    have e : vp / vb - X = ((vp - S * X * Z) - X * (vb - S * Z)) / vb := by
      field_simp
      ring
    rw [e, abs_div, abs_of_pos hvb0, div_le_iff₀ hvb0]
    have hR : 0 ≤ e3 * X + 1 / 2 ^ 1063 := by positivity
    calc |(vp - S * X * Z) - X * (vb - S * Z)| ≤ (E2 + Eb) * (S * X * Z) + 1 / 2 ^ 1071 := hnum
      _ ≤ (e3 * X + 1 / 2 ^ 1063) * ((1 - Eb) * (S * Z)) := by
          rw [he3]
          linarith [mul_nonneg hP0 hk1]
      _ ≤ (e3 * X + 1 / 2 ^ 1063) * vb := mul_le_mul_of_nonneg_left hvb hR
  have hpb : |vp / vb| ≤ X + (e3 * X + 1 / 2 ^ 1063) := by
    have := abs_sub_abs_le_abs_sub (vp / vb) X
    rw [abs_of_nonneg hX0] at this
    linarith
  have h4 := abs_sub_le vq (vp / vb) X
  have h5 : |vp / vb| / 2 ^ 53 ≤ (X + (e3 * X + 1 / 2 ^ 1063)) / 2 ^ 53 :=
    div_le_div_of_nonneg_right hpb (by positivity)
  rw [← he3]
  have e : (X + (e3 * X + 1 / 2 ^ 1063)) / 2 ^ 53 = (1 + e3) / 2 ^ 53 * X + 1 / 2 ^ 1116 := by
    ring
  linarith

/-- The constant of the two relative bounds. -/
theorem final_const {Et Ez Eb : ℝ} (hEt0 : 0 ≤ Et) (hEz0 : 0 ≤ Ez) (hEz : Ez ≤ 1 / 2 ^ 17)
    (hEb0 : 0 ≤ Eb) :
    (((Et + Ez + Et * Ez) + (1 + 1 / 2 ^ 15) / 2 ^ 53 + Eb) * (1 + 1 / 2 ^ 16) +
      (1 + ((Et + Ez + Et * Ez) + (1 + 1 / 2 ^ 15) / 2 ^ 53 + Eb) * (1 + 1 / 2 ^ 16)) / 2 ^ 53) ≤
      (Et + Ez + Eb + 2 * (1 / 2 ^ 53)) * (1 + 1 / 2 ^ 14) := by
  obtain ⟨G, hG⟩ : ∃ G, G = Et + Ez + Eb + 1 / 2 ^ 53 := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by rw [hG]; positivity
  have k1 : Et * Ez ≤ Et / 2 ^ 17 := by
    have := mul_le_mul_of_nonneg_left hEz hEt0
    linarith
  have k2 : (Et + Ez + Et * Ez) + (1 + 1 / 2 ^ 15) / 2 ^ 53 + Eb ≤ G * (1 + 1 / 2 ^ 15) := by
    rw [hG]
    linarith
  obtain ⟨e3, he3⟩ : ∃ e, e = ((Et + Ez + Et * Ez) + (1 + 1 / 2 ^ 15) / 2 ^ 53 + Eb) *
      (1 + 1 / 2 ^ 16) := ⟨_, rfl⟩
  have k3 : e3 ≤ G * ((1 + 1 / 2 ^ 15) * (1 + 1 / 2 ^ 16)) := by
    rw [he3]
    have := mul_le_mul_of_nonneg_right k2 (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 16)
    linarith
  have k4 : G * ((1 + 1 / 2 ^ 15) * (1 + 1 / 2 ^ 16)) * (1 + 1 / 2 ^ 53) ≤ G * (1 + 1 / 2 ^ 14) := by
    have : ((1 : ℝ) + 1 / 2 ^ 15) * (1 + 1 / 2 ^ 16) * (1 + 1 / 2 ^ 53) ≤ 1 + 1 / 2 ^ 14 := by
      norm_num
    have := mul_le_mul_of_nonneg_left this hG0
    linarith
  rw [← he3]
  have k5 := mul_le_mul_of_nonneg_right k3 (by positivity : (0 : ℝ) ≤ 1 + 1 / 2 ^ 53)
  have e : (Et + Ez + Eb + 2 * (1 / 2 ^ 53)) * (1 + 1 / 2 ^ 14) =
      G * (1 + 1 / 2 ^ 14) + 1 / 2 ^ 53 * (1 + 1 / 2 ^ 14) := by rw [hG]; ring
  rw [e]
  linarith

/-- `t z / b` for `t ≈ S X`, `z ≈ Z`, and `b ≈ S Z`. -/
theorem final_float {t z b : Float} {S X Z Et Ez Eb : ℝ} (htf : Finite t.toBits)
    (ht : |value t.toBits - S * X| ≤ Et * (S * X) + 1 / 2 ^ 1074)
    (hz : FApprox z Z (Ez * Z)) (hb : FApprox b (S * Z) (Eb * (S * Z)))
    (hS : 0 < S) (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hZ : 0 < Z) (hZ3 : Z ≤ 3) (hSX : S * X ≤ 2 ^ 1018)
    (hSZ : 1 / 200 ≤ S * Z) (hEt0 : 0 ≤ Et) (hEt : Et ≤ 1 / 2 ^ 17) (hEz0 : 0 ≤ Ez)
    (hEz : Ez ≤ 1 / 2 ^ 17) (hEb0 : 0 ≤ Eb) (hEb : Eb ≤ 1 / 2 ^ 17) :
    Finite (t * z / b).toBits ∧
      |value (t * z / b).toBits - X| ≤ (Et + Ez + Eb + 2 * 𝐮) * (1 + 1 / 2 ^ 14) * X +
        1 / 2 ^ 1060 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hvt : |value t.toBits| ≤ 2 ^ 1019 := by
    have h1 := abs_sub_abs_le_abs_sub (value t.toBits) (S * X)
    rw [abs_of_nonneg (by positivity : 0 ≤ S * X)] at h1
    have h2 : Et * (S * X) ≤ 1 / 2 ^ 17 * 2 ^ 1018 :=
      mul_le_mul hEt hSX (by positivity) (by norm_num)
    have h3 : (2 : ℝ) ^ 1018 + 1 / 2 ^ 17 * 2 ^ 1018 + 1 / 2 ^ 1074 ≤ 2 ^ 1019 := by norm_num
    linarith
  have hvz : |value z.toBits| ≤ 4 := by
    have h1 := Approx.mag hz
    rw [abs_of_pos hZ] at h1
    have := mul_le_mul hEz hZ3 hZ.le (by norm_num)
    linarith
  have hp := fapprox_mul (fapprox_exact t htf) (fapprox_exact z hz.1) |value t.toBits|
    |value z.toBits| le_rfl le_rfl (|value t.toBits| * |value z.toBits|) (by simp) (by
      have := mul_le_mul hvt hvz (abs_nonneg _) (by positivity)
      linarith [show (2 : ℝ) ^ 1019 * 4 < 2 ^ 1022 by norm_num])
  have hp2 : |value (t * z).toBits - value t.toBits * value z.toBits| ≤
      |value t.toBits * value z.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have := hp.2
    rw [abs_mul]
    simp only [zero_mul, mul_zero, add_zero, zero_add] at this
    linarith
  have hP := prod_rel hS hX0 hZ hZ3 hEt0 hEt hEz0 hEz ht hz.2 hp2
  obtain ⟨E2, hE2⟩ : ∃ E, E = (Et + Ez + Et * Ez) + (1 + 1 / 2 ^ 15) / 2 ^ 53 := ⟨_, rfl⟩
  rw [← hE2] at hP
  have hE20 : 0 ≤ E2 := by rw [hE2]; positivity
  have hE21 : E2 ≤ 1 / 2 ^ 14 := by
    rw [hE2]
    have := mul_le_mul hEt hEz hEz0 (by norm_num)
    linarith
  have hvb : (1 - Eb) * (S * Z) ≤ value b.toBits := by
    have := (abs_le.mp hb.2).1
    linarith
  have hB : 0 < S * Z := by positivity
  have hvb0 : 0 < value b.toBits := lt_of_lt_of_le (mul_pos (by linarith) hB) hvb
  have hvp : |value (t * z).toBits| ≤ 2 * (S * Z) + 1 / 2 ^ 1071 := by
    have h1 := abs_sub_abs_le_abs_sub (value (t * z).toBits) (S * X * Z)
    rw [abs_of_nonneg (by positivity : 0 ≤ S * X * Z)] at h1
    have h2 : S * X * Z ≤ S * Z := by nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hX1)]
    have h3 := mul_le_mul_of_nonneg_right hE21 (by positivity : 0 ≤ S * X * Z)
    linarith
  have hratio : |value (t * z).toBits| / |value b.toBits| < 2 ^ 1022 := by
    rw [abs_of_pos hvb0, div_lt_iff₀ hvb0]
    have h1 : (1 - 1 / 2 ^ 17) * (S * Z) ≤ (1 - Eb) * (S * Z) :=
      mul_le_mul_of_nonneg_right (by linarith) hB.le
    linarith
  have hq := fapprox_div (fapprox_exact _ hp.1) (fapprox_exact b hb.1) |value (t * z).toBits|
    |value b.toBits| le_rfl le_rfl (by rw [abs_of_pos hvb0]; exact hvb0)
    (|value (t * z).toBits| / |value b.toBits|) (by simp) hratio
  have hq2 : |value (t * z / b).toBits - value (t * z).toBits / value b.toBits| ≤
      |value (t * z).toBits / value b.toBits| / 2 ^ 53 + 1 / 2 ^ 1075 := by
    have := hq.2
    rw [abs_div]
    simp only [zero_mul, mul_zero, zero_div, add_zero, zero_add, sub_zero] at this
    linarith
  have hQ := quot_rel hS hX0 hZ hSZ hEb0 hEb hE20 hP hb.2 hq2
  refine ⟨hq.1, ?_⟩
  have hc := final_const hEt0 hEz0 hEz hEb0
  rw [← hE2] at hc
  rw [hu]
  have := mul_le_mul_of_nonneg_right hc hX0
  have h6 : (1 : ℝ) / 2 ^ 1062 ≤ 1 / 2 ^ 1060 := by norm_num
  linarith

/-- `j0` and `j1` on `xa` with `0 < xa < 2`. -/
theorem j01_facts (xa : Float) (hxf : Finite xa.toBits)
    (hb2 : xa.toBits.toNat < 0x4000000000000000) (hw0 : 0 < value xa.toBits) :
    Finite (Bessel.j0 xa).toBits ∧
      |value (Bessel.j0 xa).toBits - Jn 0 (value xa.toBits)| ≤ 235 / 100 * 𝐮 ∧
      Finite (Bessel.j1 xa).toBits ∧
      |value (Bessel.j1 xa).toBits - Jn 1 (value xa.toBits)| ≤ 389 / 100 * 𝐮 := by
  have h2 : xa.toBits.toNat % 2 ^ 63 < 0x4000000000000000 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    exact hb2
  obtain ⟨f0, e0⟩ := BesselJ0Small.j0_small xa hxf h2
  obtain ⟨f1, e1⟩ := BesselJ1Small.j1_small xa hxf h2
  rw [abs_of_pos hw0] at e1
  rw [Jn_zero, Jn_one]
  exact ⟨f0, e0, f1, le_trans e1 (BesselJ1Small.j1Err_le _)⟩

theorem abs_facts (x : Float) (hxf : Finite x.toBits) :
    Finite x.abs.toBits ∧ value x.abs.toBits = |value x.toBits| := by
  have hab := F64Bits.toBits_abs x
  exact ⟨by rw [hab]; exact Library.Numerics.Float64.Trig.TrigSinCos.abs_finite _ hxf, by rw [hab, Library.Numerics.Float64.Trig.TrigSinCos.abs_value]⟩

/-- Bounds on `J₀` and `J₁` below 2. -/
theorem J01_bounds (w : ℝ) (hw0 : 0 < w) (hw2 : w < 2) :
    Jn 0 w ≤ 7 / 3 ∧ Jn 1 w ≤ 5 / 3 ∧ (w ≤ 1 → 2 / 3 ≤ Jn 0 w ∧ Jn 1 w ≤ 7 / 12) := by
  have b0 := Jn_bounds 0 w hw0.le hw2.le
  have b1 := (Jn_bounds 1 w hw0.le hw2.le).2
  have f0 : ((0 : ℕ).factorial : ℝ) = 1 := by norm_num
  have f1 : ((0 + 1 : ℕ).factorial : ℝ) = 1 := by norm_num [Nat.factorial]
  have f1' : ((1 : ℕ).factorial : ℝ) = 1 := by norm_num
  have f2 : ((1 + 1 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
  rw [f0, f1, pow_zero] at b0
  rw [f1', f2, pow_one] at b1
  have hw4 : w ^ 2 ≤ 4 := by nlinarith
  have hw8 : w ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hw0.le hw2.le 3
  refine ⟨by nlinarith [b0.2], by nlinarith [b1], fun h1 => ⟨by nlinarith [b0.1], ?_⟩⟩
  have hw3 : w ^ 3 ≤ 1 := pow_le_one₀ hw0.le h1
  nlinarith [b1]

set_option maxHeartbeats 4000000 in
/-- Miller's method of `jn` for `2^-30 ≤ x < 2`. -/
theorem jn_backward (xa : Float) (n : UInt64) (hxf : Finite xa.toBits)
    (hb2 : xa.toBits.toNat < 0x4000000000000000) (hw : 1 / 2 ^ 30 ≤ value xa.toBits)
    (hn : 2 ≤ n.toNat) (hn2 : n.toNat ≤ 2 ^ 31) :
    Finite (Bessel.jnBackward Trig.invPi Trig.halfPi Log.logTable Log.logTable2 Bessel.j0Table
        Bessel.j1Table n xa).toBits ∧
      |value (Bessel.jnBackward Trig.invPi Trig.halfPi Log.logTable Log.logTable2
          Bessel.j0Table Bessel.j1Table n xa).toBits - Jn n.toNat (value xa.toBits)| ≤
        (23 + 8 * (n.toNat : ℝ)) * 𝐮 * Jn n.toNat (value xa.toBits) + 1 / 2 ^ 1060 := by
  rw [backward_eq]
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hw0 : 0 < value xa.toBits := lt_of_lt_of_le (by norm_num) hw
  have hw2 : value xa.toBits < 2 := by
    have h := F64PositiveOrder.value_strict (left := xa.toBits)
      (right := (0x4000000000000000 : UInt64)) (by decide) (by exact hb2)
    rwa [BesselJ0Large.value_two] at h
  -- the continued fraction and the flag
  obtain ⟨hW, hH⟩ := wh_facts xa n hxf hw hw2 hn hn2
  obtain ⟨K, hK1, hK13, hKw, hQ⟩ := cf_depth hw hw2 hn hn2 hW hH
  have ht0 : FApprox (tinit n xa) (Jn n.toNat (value xa.toBits) / Jn (n.toNat - 1) (value xa.toBits))
      (61 / 10 * 𝐮 * (Jn n.toNat (value xa.toBits) / Jn (n.toNat - 1) (value xa.toBits))) := by
    have hk : kOf n xa = UInt64.ofNat K := hKw
    unfold tinit
    rw [hk]
    exact t_value xa n K hxf hw hw2 hn hn2 hK1 hK13 hQ
  have h0 := binv_zero (scaleOf n xa) xa n (tinit n xa) hw hw2 hn hn2 ht0
    (flag_jn xa n hxf hw hw2 hn hn2)
  -- the backward loop
  have hsub : (n - 1).toNat = n.toNat - 2 + 1 := by
    rw [UInt64.toNat_sub]
    have := n.toNat_lt
    simp only [UInt64.reduceToNat, Nat.reducePow] at this ⊢
    omega
  have hloop : LeanExe.loop (n - 1) (tinit n xa, 1.0, tinit n xa, (2 * (n - 1)).toFloat)
      (fun _ s => bbody (scaleOf n xa) xa s) =
      bbody (scaleOf n xa) xa (lseq (fun _ s => bbody (scaleOf n xa) xa s)
        (tinit n xa, 1.0, tinit n xa, (2 * (n - 1)).toFloat) (n.toNat - 2)) := by
    rw [loop_lseq, hsub]
    rfl
  rw [hloop]
  have hs := binv_iter (scaleOf n xa) xa hxf hw hw2 n.toNat hn hn2 _ h0 (n.toNat - 2) le_rfl
  set w := value xa.toBits with hwdef
  set s := lseq (fun _ s => bbody (scaleOf n xa) xa s)
    (tinit n xa, 1.0, tinit n xa, (2 * (n - 1)).toFloat) (n.toNat - 2) with hsdef
  -- `j0`, `j1`, and the real functions
  obtain ⟨f0, e0, f1, e1⟩ := j01_facts xa hxf hb2 hw0
  obtain ⟨hv0l, hv0u⟩ := abs_le.mp e0
  obtain ⟨hv1l, hv1u⟩ := abs_le.mp e1
  obtain ⟨hJ0u, hJ1u, hJsmall⟩ := J01_bounds w hw0 hw2
  have hJ0 := Jn_pos 0 w hw0 hw2.le
  have hJ1 := Jn_pos 1 w hw0 hw2.le
  have hJn := Jn_pos n.toNat w hw0 hw2.le
  have hJ0l : 1 / 5 ≤ Jn 0 w := by
    rw [Jn_zero]
    exact LeanExe.ProofKit.BesselModulus.J0_small w (by rw [abs_of_pos hw0]; exact hw2.le)
  have hJn1 : Jn n.toNat w ≤ 1 := by
    have h1 := Jn_le n.toNat (by omega) w hw0.le hw2.le
    have h2 : (w / 2) ^ n.toNat ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have h3 : (2 : ℝ) ≤ n.toNat.factorial := by
      exact_mod_cast le_trans hn (Nat.self_le_factorial _)
    have h4 : (w / 2) ^ n.toNat / (n.toNat.factorial : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]
      linarith
    linarith
  obtain ⟨a0f, a0v⟩ := abs_facts _ f0
  obtain ⟨a1f, a1v⟩ := abs_facts _ f1
  have hz0pos : 0 < value (Bessel.j0 xa).toBits := by linarith
  have hnr : (2 : ℝ) ≤ n.toNat := by exact_mod_cast hn
  have hnb : (n.toNat : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hn2
  have hTb := Tb_le (n.toNat - 1) (by omega)
  have hTe : Tb (n.toNat - 1) = (61 / 10 + 101 / 100 * ((n.toNat : ℝ) - 1)) * 𝐮 := by
    unfold Tb
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hm : ((n.toNat - 2 : ℕ) : ℝ) = (n.toNat : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  obtain ⟨hβ0, hβ1⟩ := βB_le (n.toNat - 2) 1 (by omega)
  have hβ : βB (n.toNat - 2) 1 = (6 * ((n.toNat : ℝ) - 2) + 5) * 𝐮 := by
    unfold βB
    rw [if_pos rfl, hm]
    ring
  unfold bfinal
  split_ifs with hc
  · -- `|j0 x| ≥ |j1 x|`: divide by `b ≈ σ J₀`
    have hcv := (fle_iff _ _ a1f a0f).mp hc
    rw [a0v, a1v, abs_of_pos hz0pos] at hcv
    have hj1 := le_abs_self (value (Bessel.j1 xa).toBits)
    have hJ01' : Jn 1 w ≤ Jn 0 w + 624 / 100 * 𝐮 := by linarith
    have hJ01 : Jn 1 w ≤ Jn 0 w + 1 / 2 ^ 40 := by linarith
    obtain ⟨σ, hσ, hbJ, -, htf, ht, -, hσJ0, hσn⟩ :=
      last_step (scaleOf n xa) xa hxf hw hw2 n.toNat hn hn2 s hs (21 / 20) (by norm_num)
        (by norm_num) (d_one w hw0 hw2 hJ01)
    have hJ0l' : 2 / 5 - 7 * 𝐮 ≤ Jn 0 w := by
      rcases le_or_gt w 1 with h1 | h1
      · have := (hJsmall h1).1
        linarith
      · have h2 := LeanExe.ProofKit.BesselModulus.J1_mid w h1.le hw2.le
        rw [← Jn_one] at h2
        linarith
    have hz : FApprox (Bessel.j0 xa) (Jn 0 w) (59 / 10 * 𝐮 * Jn 0 w) := by
      refine ⟨f0, le_trans e0 ?_⟩
      rw [hu] at hJ0l' ⊢
      linarith
    have hK : KL (21 / 20) ≤ 17775 / 1000 * 𝐮 := by
      unfold KL
      rw [hu]
      norm_num
    have hK0 : 0 ≤ KL (21 / 20) := (KL_le (21 / 20) (by norm_num) (by norm_num)).1
    have hβL : βL (21 / 20) n.toNat ≤ (1778 / 100 + 6 * ((n.toNat : ℝ) - 2) + 5) * 𝐮 := by
      unfold βL
      rw [hβ] at hβ1 ⊢
      have h1 := mul_le_mul_of_nonneg_left hβ1 hK0
      have h2 : KL (21 / 20) * (1 / 2 ^ 18) ≤ 1 / 200 * 𝐮 := by rw [hu] at hK ⊢; linarith
      linarith
    have hβL0 : 0 ≤ βL (21 / 20) n.toNat := by
      unfold βL
      positivity
    have hβL1 : βL (21 / 20) n.toNat ≤ 1 / 2 ^ 17 := by
      rw [hu] at hβL
      linarith
    have hf := final_float htf ht hz hbJ hσ hJn.le hJn1 hJ0 (by linarith) hσn
      (by linarith) hTb.1 (le_trans hTb.2 (by norm_num)) (by positivity)
      (by rw [hu]; norm_num) hβL0 hβL1
    refine ⟨hf.1, le_trans hf.2 ?_⟩
    have hconst : (Tb (n.toNat - 1) + 59 / 10 * 𝐮 + βL (21 / 20) n.toNat + 2 * 𝐮) *
        (1 + 1 / 2 ^ 14) ≤ (23 + 8 * (n.toNat : ℝ)) * 𝐮 := by
      rw [hTe]
      rw [hu] at hβL ⊢
      linarith
    have := mul_le_mul_of_nonneg_right hconst hJn.le
    linarith
  · -- `|j0 x| < |j1 x|`: divide by `a ≈ σ J₁`
    have hcv : |value (Bessel.j0 xa).toBits| < |value (Bessel.j1 xa).toBits| := by
      have := mt (fle_iff _ _ a1f a0f).mpr hc
      rw [a0v, a1v] at this
      exact not_le.mp this
    rw [abs_of_pos hz0pos] at hcv
    have hj1 : |value (Bessel.j1 xa).toBits| ≤ Jn 1 w + 389 / 100 * 𝐮 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hw1 : 1 < w := by
      by_contra h1
      push_neg at h1
      obtain ⟨h2, h3⟩ := hJsmall h1
      linarith
    have hJ1l : 2 / 5 ≤ Jn 1 w := by
      have := LeanExe.ProofKit.BesselModulus.J1_mid w hw1.le hw2.le
      rwa [← Jn_one] at this
    have hdJ : Jn 2 w ≤ 25 / 6 * Jn 0 w := by
      have h1 := Jn_le 2 (by norm_num) w hw0.le hw2.le
      have hf2 : ((2 : ℕ).factorial : ℝ) = 2 := by norm_num [Nat.factorial]
      rw [hf2] at h1
      have h2 : (w / 2) ^ 2 ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
      linarith
    obtain ⟨σ, hσ, -, haJ, htf, ht, -, hσJ0, hσn⟩ :=
      last_step (scaleOf n xa) xa hxf hw hw2 n.toNat hn hn2 s hs (25 / 6) (by norm_num)
        (by norm_num) hdJ
    have hz : FApprox (Bessel.j1 xa) (Jn 1 w) (975 / 100 * 𝐮 * Jn 1 w) := by
      refine ⟨f1, le_trans e1 ?_⟩
      rw [hu]
      linarith
    have hσJ1 : 1 / 200 ≤ σ * Jn 1 w := by
      have h1 : 1 / 20 * Jn 1 w ≤ σ * Jn 0 w * Jn 1 w := mul_le_mul_of_nonneg_right hσJ0 hJ1.le
      have h2 : σ * Jn 1 w * Jn 0 w ≤ σ * Jn 1 w * (7 / 3) :=
        mul_le_mul_of_nonneg_left hJ0u (by positivity)
      linarith
    have hf := final_float htf ht hz haJ hσ hJn.le hJn1 hJ1 (by linarith) hσn
      hσJ1 hTb.1 (le_trans hTb.2 (by norm_num)) (by positivity)
      (by rw [hu]; norm_num) (by positivity) (by linarith)
    refine ⟨hf.1, le_trans hf.2 ?_⟩
    have hconst : (Tb (n.toNat - 1) + 975 / 100 * 𝐮 + (βB (n.toNat - 2) 1 + 2 * 𝐮) + 2 * 𝐮) *
        (1 + 1 / 2 ^ 14) ≤ (23 + 8 * (n.toNat : ℝ)) * 𝐮 := by
      rw [hTe, hβ, hu]
      linarith
    have := mul_le_mul_of_nonneg_right hconst hJn.le
    linarith

#print axioms backward_eq
#print axioms small_flag
#print axioms final_float
#print axioms jn_backward

end Library.Numerics.Float64.Bessel.BesselMillerFinal
