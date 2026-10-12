import Verified.Examples.BesselMillerStep
import Verified.Examples.BesselMillerT
import Verified.Examples.BesselMillerLog
import Verified.Examples.BesselJ0Large
import Verified.Examples.TrigSinCos

/-!
The loop of `jn`'s backward recurrence up to `J₁`.  The state `(a, b, t, dᵢ)` after `m` steps
stands for `σ (J_(i+1), J_i, J_n, 2i)` with `i = n - 1 - m` and a scale `σ > 0` that changes only
when the code divides by `b' > 10^100` (`BInv`).  The invariant bounds the relative error of `b` by
`6 m u` (plus `5 u` at `i = 1`), that of `a` by `(6 m + 7) u`, that of the ratio `b/a` against
`J_i/J_(i+1)` by `7 u` (`12 u` at `i = 1`), and that of `t` by `(6.1 + 1.01 m) u` plus `2^-1074`;
it keeps `σ J_i ≥ 1/2`, `σ ≤ 2^1017` when the code does not scale, and `b ≤ 10^100` when it does.
The start satisfies it (`binv_zero`), and `BesselMillerStep.bstep` with `d ≤ 1/5` from `i = 3` on
and `d ≤ 2/3` at `i = 2` keeps it through each step down to `i = 1` (`binv_step`).
-/

namespace Verified.Examples.BesselMillerBack
open Real CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound BesselPQEval BesselOrderN BesselRecur
  BesselStepF BesselJnTiny BesselSmallSigns BesselMillerReal BesselMillerCF BesselMillerFacts
  BesselMillerStep BesselMillerT BesselMillerLog

local notation "𝐮" => unitRoundoff64

set_option exponentiation.threshold 2048

/-- The body of the backward loop. -/
def bbody (scale : Bool) (x : Float) (s : Float × Float × Float × Float) :
    Float × Float × Float × Float :=
  if scale && (s.2.1 * s.2.2.2 / x - s.1) > Float.ofBits 0x54B249AD2594C37D then
    (s.2.1 / (s.2.1 * s.2.2.2 / x - s.1), 1.0, s.2.2.1 / (s.2.1 * s.2.2.2 / x - s.1), s.2.2.2 - 2.0)
  else (s.2.1, s.2.1 * s.2.2.2 / x - s.1, s.2.2.1, s.2.2.2 - 2.0)

noncomputable def βB (m i : ℕ) : ℝ := 6 * 𝐮 * m + (if i = 1 then 5 * 𝐮 else 0)

noncomputable def αB (m : ℕ) : ℝ := 6 * 𝐮 * m + 7 * 𝐮

noncomputable def Er (i : ℕ) : ℝ := if i = 1 then 12 * 𝐮 else 7 * 𝐮

noncomputable def Tb (m : ℕ) : ℝ := 61 / 10 * 𝐮 + 101 / 100 * 𝐮 * m

/-- The invariant of the backward loop after `m` steps, with `i = n - 1 - m`. -/
def BInv (scale : Bool) (w : ℝ) (n m : ℕ) (s : Float × Float × Float × Float) : Prop :=
  ∃ σ : ℝ, 0 < σ ∧
    FApprox s.2.2.2 (2 * ((n - 1 - m : ℕ) : ℝ)) 0 ∧
    FApprox s.2.1 (σ * Jn (n - 1 - m) w) (βB m (n - 1 - m) * (σ * Jn (n - 1 - m) w)) ∧
    FApprox s.1 (σ * Jn (n - m) w) (αB m * (σ * Jn (n - m) w)) ∧
    |value s.2.1.toBits * Jn (n - m) w - value s.1.toBits * Jn (n - 1 - m) w| ≤
      Er (n - 1 - m) * (value s.1.toBits * Jn (n - 1 - m) w) ∧
    Finite s.2.2.1.toBits ∧
    |value s.2.2.1.toBits - σ * Jn n w| ≤ Tb m * (σ * Jn n w) + 1 / 2 ^ 1074 ∧
    1 / 2 ≤ σ * Jn (n - 1 - m) w ∧
    (scale = false → σ ≤ 2 ^ 1017) ∧
    (scale = true → value s.2.1.toBits ≤ 2 ^ 333)

/-- An integer difference of floats is exact. -/
theorem int_sub_exact (a b : Float) (ha : Finite a.toBits) (hb : Finite b.toBits) (A B : ℤ)
    (hA : value a.toBits = A) (hB : value b.toBits = B) (hAB : |A - B| ≤ 2 ^ 53) :
    Finite (a - b).toBits ∧ value (a - b).toBits = A - B := by
  rw [F64Bits.toBits_sub]
  have hs : ∀ (c : UInt64) (C : ℤ), value c = C → Wasm.IEEE64.scaledValue c = C * 2 ^ 1074 := by
    intro c C hc
    have : (Wasm.IEEE64.scaledValue c : ℝ) = ((C * 2 ^ 1074 : ℤ) : ℝ) := by
      rw [value] at hc
      push_cast
      field_simp at hc
      linarith
    exact_mod_cast this
  have hsa := hs _ A hA
  have hsb := hs _ B hB
  have h := F64ErrorTrack.sub_exact_grid a.toBits b.toBits ha hb 1074 (by norm_num)
    ⟨A, by rw [hsa]; ring⟩ ⟨B, by rw [hsb]; ring⟩ (by
      rw [hsa, hsb, show A * 2 ^ 1074 - B * 2 ^ 1074 = (A - B) * 2 ^ 1074 by ring, abs_mul]
      have : |(2 : ℤ) ^ 1074| = 2 ^ 1074 := abs_of_pos (by positivity)
      rw [this]
      exact mul_le_mul_of_nonneg_right hAB (by positivity))
  refine ⟨h.1, ?_⟩
  rw [h.2, hA, hB]

theorem two_f : Finite (2.0 : Float).toBits ∧ value (2.0 : Float).toBits = (2 : ℤ) := by
  have h := BesselMillerDepth.value_two_f
  refine ⟨h.1, ?_⟩
  have := abs_nonpos_iff.mp h.2
  push_cast
  linarith

/-- The step of `dᵢ`: `2 i - 2` exactly. -/
theorem di_step {di : Float} (i : ℕ) (hi : 1 ≤ i) (hi2 : i ≤ 2 ^ 31) (h : FApprox di (2 * (i : ℝ)) 0) :
    FApprox (di - 2.0) (2 * ((i - 1 : ℕ) : ℝ)) 0 := by
  have hv : value di.toBits = ((2 * (i : ℤ) : ℤ) : ℝ) := by
    have := abs_nonpos_iff.mp h.2; push_cast; linarith
  have hiz : (i : ℤ) ≤ 2 ^ 31 := by exact_mod_cast hi2
  have hiz1 : (1 : ℤ) ≤ i := by exact_mod_cast hi
  obtain ⟨hf, hv2⟩ := int_sub_exact di 2.0 h.1 two_f.1 (2 * (i : ℤ)) 2 hv two_f.2 (by
    rw [abs_le]; constructor <;> nlinarith)
  refine ⟨hf, ?_⟩
  rw [hv2]
  have e : ((2 * (i : ℤ) : ℤ) : ℝ) - ((2 : ℤ) : ℝ) - 2 * ((i - 1 : ℕ) : ℝ) = 0 := by
    push_cast [Nat.cast_sub hi]; ring
  rw [e, abs_zero]

/-- The bounds of the constant `10^100` of the code. -/
theorem c100_facts : Finite (Float.ofBits 0x54B249AD2594C37D).toBits ∧
    2 ^ 332 ≤ value (Float.ofBits 0x54B249AD2594C37D).toBits ∧
    value (Float.ofBits 0x54B249AD2594C37D).toBits ≤ 2 ^ 333 := by
  have hfin : Finite (0x54B249AD2594C37D : UInt64) := by unfold CodeLib.IEEE64.Finite; decide
  have h := fapprox_ofBits _ hfin
  have hv := abs_nonpos_iff.mp h.2
  have hq : value (0x54B249AD2594C37D : UInt64) = ratOfWord 0x54B249AD2594C37D := (ratOfWord_cast _).symm
  have h1 : (2 : ℚ) ^ 332 ≤ ratOfWord 0x54B249AD2594C37D := by decide +kernel
  have h2 : ratOfWord 0x54B249AD2594C37D ≤ (2 : ℚ) ^ 333 := by decide +kernel
  have h1' : (2 : ℝ) ^ 332 ≤ (ratOfWord 0x54B249AD2594C37D : ℝ) := by exact_mod_cast h1
  have h2' : (ratOfWord 0x54B249AD2594C37D : ℝ) ≤ 2 ^ 333 := by exact_mod_cast h2
  refine ⟨h.1, ?_, ?_⟩ <;> linarith

/-- The start `(t₀, 1, t₀, 2 (n - 1))` with `σ = 1/J_(n-1)`. -/
theorem binv_zero (scale : Bool) (xa : Float) (n : UInt64) (t0 : Float)
    (hw : 1 / 2 ^ 30 ≤ value xa.toBits) (hw2 : value xa.toBits < 2) (hn : 2 ≤ n.toNat)
    (hn2 : n.toNat ≤ 2 ^ 31)
    (ht0 : FApprox t0 (Jn n.toNat (value xa.toBits) / Jn (n.toNat - 1) (value xa.toBits))
      (61 / 10 * 𝐮 * (Jn n.toNat (value xa.toBits) / Jn (n.toNat - 1) (value xa.toBits))))
    (hflag : scale = false → 1 / Jn (n.toNat - 1) (value xa.toBits) ≤ 2 ^ 1017) :
    BInv scale (value xa.toBits) n.toNat 0 (t0, 1.0, t0, (2 * (n - 1)).toFloat) := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hJ1 := Jn_pos (n.toNat - 1) w hw0 hw2.le
  have hJn := Jn_pos n.toNat w hw0 hw2.le
  set σ := 1 / Jn (n.toNat - 1) w with hσ
  have hσ0 : 0 < σ := by positivity
  have hσJ : σ * Jn (n.toNat - 1) w = 1 := by rw [hσ]; field_simp
  set r := Jn n.toNat w / Jn (n.toNat - 1) w with hr
  have hσr : σ * Jn n.toNat w = r := by rw [hσ, hr]; ring
  have hr0 : 0 < r := by positivity
  have hnn : (2 * (n - 1)).toNat = 2 * (n.toNat - 1) := by
    rw [UInt64.toNat_mul, UInt64.toNat_sub]
    have := n.toNat_lt
    simp only [UInt64.reduceToNat, Nat.reducePow] at this ⊢
    omega
  have hdi := toFloat_exact (2 * (n - 1)) (by rw [hnn]; omega)
  rw [hnn] at hdi
  have hone := fapprox_one
  have hv1 : value (1.0 : Float).toBits = 1 := by
    have := abs_nonpos_iff.mp hone.2; linarith
  unfold BInv
  simp only [Nat.sub_zero]
  refine ⟨σ, hσ0, ?_, ?_, ?_, ?_, ht0.1, ?_, ?_, ?_, ?_⟩
  · show FApprox (2 * (n - 1)).toFloat (2 * ((n.toNat - 1 : ℕ) : ℝ)) 0
    have e : ((2 * (n.toNat - 1) : ℕ) : ℝ) = 2 * ((n.toNat - 1 : ℕ) : ℝ) := by push_cast; ring
    rw [← e]; exact hdi
  · show FApprox 1.0 (σ * Jn (n.toNat - 1) w) (βB 0 (n.toNat - 1) * (σ * Jn (n.toNat - 1) w))
    rw [hσJ]
    refine fmono hone ?_
    unfold βB; split_ifs <;> nlinarith [hu0]
  · show FApprox t0 (σ * Jn n.toNat w) (αB 0 * (σ * Jn n.toNat w))
    rw [hσr]
    refine fmono ht0 ?_
    unfold αB; push_cast; rw [hu]; nlinarith
  · show |value (1.0 : Float).toBits * Jn n.toNat w - value t0.toBits * Jn (n.toNat - 1) w| ≤
      Er (n.toNat - 1) * (value t0.toBits * Jn (n.toNat - 1) w)
    rw [hv1]
    have h2 := ht0.2
    have hlow : r * (1 - 61 / 10 * 𝐮) ≤ value t0.toBits := by
      have := (abs_le.mp h2).1; nlinarith
    have e : 1 * Jn n.toNat w - value t0.toBits * Jn (n.toNat - 1) w =
        (r - value t0.toBits) * Jn (n.toNat - 1) w := by rw [hr]; field_simp
    rw [e, abs_mul, abs_of_pos hJ1, abs_sub_comm]
    have hEr : 7 * 𝐮 ≤ Er (n.toNat - 1) := by unfold Er; split_ifs <;> rw [hu] <;> norm_num
    have h3 : |value t0.toBits - r| ≤ 7 * 𝐮 * value t0.toBits := by
      rw [hu] at hlow ⊢
      have : 61 / 10 * (1 / 2 ^ 53) * r ≤ 7 * (1 / 2 ^ 53) * value t0.toBits := by nlinarith
      rw [hu] at h2
      linarith
    have h4 := mul_le_mul_of_nonneg_right h3 hJ1.le
    have h5 : 7 * 𝐮 * value t0.toBits * Jn (n.toNat - 1) w ≤
        Er (n.toNat - 1) * (value t0.toBits * Jn (n.toNat - 1) w) := by
      have : 0 ≤ value t0.toBits * Jn (n.toNat - 1) w := by
        have : 0 ≤ value t0.toBits := by rw [hu] at hlow; nlinarith
        positivity
      nlinarith
    linarith
  · rw [hσr]
    have := ht0.2
    unfold Tb
    push_cast
    nlinarith
  · rw [hσJ]; norm_num
  · intro h; rw [hσ]; exact hflag h
  · intro _; show value (1.0 : Float).toBits ≤ 2 ^ 333; rw [hv1]; norm_num

/-- The bound of `bstep`'s factor with `E = 7 u`. -/
theorem K_bound (d : ℝ) (hd0 : 0 ≤ d) (i : ℕ)
    (hd : d = if i = 2 then 2 / 3 else 1 / 5) :
    (1 + d) * (203 / 100) * 𝐮 + d * (7 * 𝐮) * (1 + 2 * (7 * 𝐮)) + 101 / 100 * 𝐮 ≤
      (if i = 2 then 91 / 10 * 𝐮 else 49 / 10 * 𝐮) := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  rw [hu]
  split_ifs at hd ⊢ with h <;> rw [hd] <;> norm_num

/-- The error of `b` after a step, from that of `T`. -/
theorem b_err {b' B T σJ σJm Ji Jim K β : ℝ} (hJi : 0 < Ji) (hJim : 0 < Jim) (hσJ : 0 < σJ)
    (hT : T = B * Jim / Ji) (hσJm : σJm = σJ * Jim / Ji) (hK : 0 ≤ K) (hβ : 0 ≤ β)
    (h1 : |b' - T| ≤ K * T) (h2 : |B - σJ| ≤ β * σJ) :
    |b' - σJm| ≤ (K * (1 + β) + β) * σJm := by
  have hTσ : T - σJm = (B - σJ) * Jim / Ji := by rw [hT, hσJm]; ring
  have hc : 0 < Jim / Ji := div_pos hJim hJi
  have h3 : |T - σJm| ≤ β * σJm := by
    rw [hTσ, abs_div, abs_mul, abs_of_pos hJim, abs_of_pos hJi, hσJm]
    have := mul_le_mul_of_nonneg_right h2 hJim.le
    rw [div_le_iff₀ hJi]
    have e : β * (σJ * Jim / Ji) * Ji = β * σJ * Jim := by field_simp
    nlinarith
  have hTle : T ≤ (1 + β) * σJm := by
    have := (abs_le.mp h3).2; nlinarith
  have := abs_sub_le b' T σJm
  have h4 : K * T ≤ K * ((1 + β) * σJm) := mul_le_mul_of_nonneg_left hTle hK
  nlinarith

/-- The comparison with the constant `10^100`. -/
theorem gt_c100 (b : Float) (hb : Finite b.toBits) :
    (b > Float.ofBits 0x54B249AD2594C37D) ↔ value (Float.ofBits 0x54B249AD2594C37D).toBits < value b.toBits :=
  BesselSmallJ0.flt_iff _ _ c100_facts.1 hb

theorem βB_le (m i : ℕ) (hm : m ≤ 2 ^ 31) : 0 ≤ βB m i ∧ βB m i ≤ 1 / 2 ^ 18 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hmr : (m : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold βB
  rw [hu]
  split_ifs <;> constructor <;> nlinarith

theorem αB_le (m : ℕ) (hm : m ≤ 2 ^ 31) : 0 ≤ αB m ∧ αB m ≤ 1 / 2 ^ 18 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hmr : (m : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold αB
  rw [hu]
  constructor <;> nlinarith

theorem Tb_le (m : ℕ) (hm : m ≤ 2 ^ 31) : 0 ≤ Tb m ∧ Tb m ≤ 1 / 2 ^ 18 := by
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hmr : (m : ℝ) ≤ 2 ^ 31 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold Tb
  rw [hu]
  constructor <;> nlinarith

/-- The scaled `b = 1` against `σ' J_(i-1)` with `σ' = σ/b'`. -/
theorem scale_b {Bp X β : ℝ} (hBp : 0 < Bp) (hX : 0 < X) (h : |Bp - X| ≤ β * X) :
    |1 - X / Bp| ≤ β * (X / Bp) := by
  rw [show 1 - X / Bp = (Bp - X) / Bp by field_simp, abs_div, abs_of_pos hBp,
    show β * (X / Bp) = β * X / Bp by ring]
  exact div_le_div_of_nonneg_right h hBp.le

/-- The scaled `a = b ⊘ b'` against `σ' J_i`. -/
theorem scale_a {va B Bp Y β α : ℝ} (hBp : 0 < Bp) (hY : 0 < Y) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hYB : 1 / 2 ^ 64 ≤ Y / Bp)
    (hva : |va - B / Bp| ≤ B / Bp / 2 ^ 53 + 1 / 2 ^ 1075) (hB : |B - Y| ≤ β * Y)
    (hα : (1 + β) * (1 / 2 ^ 53) + β + 1 / 2 ^ 900 ≤ α) :
    |va - Y / Bp| ≤ α * (Y / Bp) := by
  have h1 : |B / Bp - Y / Bp| ≤ β * (Y / Bp) := by
    rw [show B / Bp - Y / Bp = (B - Y) / Bp by ring, abs_div, abs_of_pos hBp,
      show β * (Y / Bp) = β * Y / Bp by ring]
    exact div_le_div_of_nonneg_right hB hBp.le
  have h2 : B / Bp ≤ (1 + β) * (Y / Bp) := by have := (abs_le.mp h1).2; linarith
  have h3 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 900 * (Y / Bp) := by
    have : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 900 * (1 / 2 ^ 64) := by norm_num
    nlinarith
  have := abs_sub_le va (B / Bp) (Y / Bp)
  have h4 : B / Bp / 2 ^ 53 ≤ (1 + β) * (Y / Bp) * (1 / 2 ^ 53) := by
    rw [div_eq_mul_one_div (B / Bp)]
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have h5 := mul_le_mul_of_nonneg_right hα (show 0 ≤ Y / Bp by positivity)
  nlinarith

/-- The ratio after scaling: `|J_i - a J_(i-1)| ≤ E a J_(i-1)` for `a ≈ b/b'`. -/
theorem scale_ratio {va B Bp T J Jm K E : ℝ} (hBp : 0 < Bp) (hJ : 0 < J) (hJm : 0 < Jm)
    (hB : 0 < B) (hT : T = B * Jm / J) (hK0 : 0 ≤ K)
    (hbe : |Bp - T| ≤ K * T) (hq : 1 / 2 ^ 70 ≤ B / Bp)
    (hva : |va - B / Bp| ≤ B / Bp / 2 ^ 53 + 1 / 2 ^ 1075)
    (hE : K + 2 * (1 / 2 ^ 53) ≤ E * (1 - 2 / 2 ^ 53)) :
    |1 * J - va * Jm| ≤ E * (va * Jm) := by
  set q := B / Bp with hqdef
  have hq0 : 0 < q := by positivity
  have hqJm : q * Jm = T * J / Bp := by rw [hqdef, hT]; field_simp
  have hT0 : 0 < T := by rw [hT]; positivity
  have h1 : |J - q * Jm| ≤ K * (q * Jm) := by
    rw [hqJm, show J - T * J / Bp = J * (Bp - T) / Bp by field_simp, abs_div, abs_mul,
      abs_of_pos hJ, abs_of_pos hBp, div_le_iff₀ hBp]
    have e : K * (T * J / Bp) * Bp = K * T * J := by field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hbe hJ.le
    nlinarith
  have h3 : |q * Jm - va * Jm| ≤ (q / 2 ^ 53 + 1 / 2 ^ 1075) * Jm := by
    rw [← sub_mul, abs_mul, abs_of_pos hJm, abs_sub_comm]
    exact mul_le_mul_of_nonneg_right hva hJm.le
  have h4 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * q := by
    have : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 1000 * (1 / 2 ^ 70) := by norm_num
    nlinarith
  have h5 : q * (1 - 2 / 2 ^ 53) ≤ va := by
    have := (abs_le.mp hva).1
    have : (1 : ℝ) / 2 ^ 1075 ≤ q / 2 ^ 53 := by nlinarith
    nlinarith
  have hE0 : 0 ≤ E := by
    by_contra hc
    push Not at hc
    have : E * (1 - 2 / 2 ^ 53) < 0 := mul_neg_of_neg_of_pos hc (by norm_num)
    have : 0 ≤ K + 2 * (1 / 2 ^ 53) := by positivity
    linarith
  have h6 : E * (q * (1 - 2 / 2 ^ 53)) * Jm ≤ E * (va * Jm) := by
    have := mul_le_mul_of_nonneg_left h5 hE0
    have := mul_le_mul_of_nonneg_right this hJm.le
    linarith
  have h7 : (q / 2 ^ 53 + 1 / 2 ^ 1075) * Jm ≤ (q * (1 / 2 ^ 53) + 1 / 2 ^ 1000 * q) * Jm := by
    apply mul_le_mul_of_nonneg_right _ hJm.le
    rw [div_eq_mul_one_div q]
    linarith
  have h8 : (K + 2 * (1 / 2 ^ 53)) * (q * Jm) ≤ E * (1 - 2 / 2 ^ 53) * (q * Jm) :=
    mul_le_mul_of_nonneg_right hE (by positivity)
  have htri := abs_sub_le (1 * J) (q * Jm) (va * Jm)
  rw [one_mul] at htri ⊢
  have hqJm0 : 0 < q * Jm := by positivity
  nlinarith

/-- The scaled `t = t ⊘ b'` against `σ' J_n`. -/
theorem scale_t {vt t' Bp X Tm : ℝ} (hBp : 2 ^ 332 ≤ Bp) (hX : 0 ≤ X) (hTm0 : 0 ≤ Tm)
    (hTm1 : Tm ≤ 1 / 2 ^ 18)
    (ht : |vt - X| ≤ Tm * X + 1 / 2 ^ 1074) (ht' : |t' - vt / Bp| ≤ |vt| / Bp / 2 ^ 53 + 1 / 2 ^ 1075) :
    |t' - X / Bp| ≤ (Tm + 101 / 100 * (1 / 2 ^ 53)) * (X / Bp) + 1 / 2 ^ 1074 := by
  have hBp0 : 0 < Bp := lt_of_lt_of_le (by positivity) hBp
  have h1 : |vt / Bp - X / Bp| ≤ Tm * (X / Bp) + 1 / 2 ^ 1074 / Bp := by
    rw [show vt / Bp - X / Bp = (vt - X) / Bp by ring, abs_div, abs_of_pos hBp0,
      show Tm * (X / Bp) + 1 / 2 ^ 1074 / Bp = (Tm * X + 1 / 2 ^ 1074) / Bp by ring]
    exact div_le_div_of_nonneg_right ht hBp0.le
  have h2 : |vt| ≤ X * (1 + Tm) + 1 / 2 ^ 1074 := by
    have := abs_sub_abs_le_abs_sub vt X
    rw [abs_of_nonneg hX] at this
    linarith
  have h3 : |vt| / Bp / 2 ^ 53 ≤ (X / Bp) * (1 + Tm) * (1 / 2 ^ 53) + 1 / 2 ^ 1074 / Bp / 2 ^ 53 := by
    have : |vt| / Bp ≤ (X * (1 + Tm) + 1 / 2 ^ 1074) / Bp := div_le_div_of_nonneg_right h2 hBp0.le
    have e : (X * (1 + Tm) + 1 / 2 ^ 1074) / Bp / 2 ^ 53 =
        (X / Bp) * (1 + Tm) * (1 / 2 ^ 53) + 1 / 2 ^ 1074 / Bp / 2 ^ 53 := by ring
    rw [← e]
    exact div_le_div_of_nonneg_right this (by positivity)
  have h4 : (1 : ℝ) / 2 ^ 1074 / Bp ≤ 1 / 2 ^ 1074 / 2 ^ 332 := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) hBp
  have h5 : (1 : ℝ) / 2 ^ 1074 / 2 ^ 332 + 1 / 2 ^ 1074 / 2 ^ 332 / 2 ^ 53 + 1 / 2 ^ 1075 ≤
      1 / 2 ^ 1074 := by norm_num
  have h6 : (1 : ℝ) / 2 ^ 1074 / Bp / 2 ^ 53 ≤ 1 / 2 ^ 1074 / 2 ^ 332 / 2 ^ 53 :=
    div_le_div_of_nonneg_right h4 (by positivity)
  have hXB : 0 ≤ X / Bp := by positivity
  have h7 : (X / Bp) * (1 + Tm) * (1 / 2 ^ 53) ≤ (X / Bp) * (101 / 100 * (1 / 2 ^ 53)) := by
    have : (1 + Tm) * (1 / 2 ^ 53) ≤ 101 / 100 * (1 / 2 ^ 53) := by
      have : 1 + Tm ≤ 101 / 100 := by linarith [show (1 : ℝ) / 2 ^ 18 ≤ 1 / 100 by norm_num]
      nlinarith
    nlinarith
  have := abs_sub_le t' (vt / Bp) (X / Bp)
  nlinarith

/-- A finite word has magnitude at most `2^1024`. -/
theorem abs_value_le (x : Float) (hxf : Finite x.toBits) : |value x.toBits| ≤ 2 ^ 1024 := by
  have hab := F64Bits.toBits_abs x
  have hN := TrigSinCos.abs_toNat x.toBits
  have hfin := TrigSinCos.finite_bound x.toBits hxf
  have h := F64PositiveOrder.value_strict (left := x.abs.toBits)
    (right := (0x7FF0000000000000 : UInt64)) (by decide) (by rw [hab, hN]; exact hfin)
  rw [BesselJ0Large.value_top, hab, TrigSinCos.abs_value] at h
  exact h.le

/-- The quotient of a finite float by `b' ≥ 2^332` stays below `2^1000`. -/
theorem hAm {t : Float} {Bp : ℝ} (htf : Finite t.toBits) (hBp0 : 0 < Bp) (hBp : 2 ^ 332 ≤ Bp) :
    |value t.toBits| / Bp ≤ 2 ^ 1000 := by
  have := abs_value_le t htf
  rw [div_le_iff₀ hBp0]
  nlinarith

set_option maxHeartbeats 4000000 in
/-- One step of the backward loop down to `i - 1 ≥ 1`. -/
theorem binv_step (scale : Bool) (xa : Float) (hxf : Finite xa.toBits)
    (hw : 1 / 2 ^ 30 ≤ value xa.toBits) (hw2 : value xa.toBits < 2) (n : ℕ) (hn2 : n ≤ 2 ^ 31)
    (m : ℕ) (hm : m + 3 ≤ n) (s : Float × Float × Float × Float)
    (hs : BInv scale (value xa.toBits) n m s) :
    BInv scale (value xa.toBits) n (m + 1) (bbody scale xa s) := by
  set w := value xa.toBits with hwdef
  have hw0 : 0 < w := lt_of_lt_of_le (by norm_num) hw
  have hu : 𝐮 = 1 / 2 ^ 53 := rfl
  have hu0 : (0 : ℝ) ≤ 𝐮 := by rw [hu]; positivity
  have hx : FApprox xa w 0 := by rw [hwdef]; exact fapprox_exact xa hxf
  obtain ⟨σ, hσ, hdi, hb, ha, hr, htf, ht, hlow, hsf, hst⟩ := hs
  obtain ⟨i, hi⟩ : ∃ i, i = n - 1 - m := ⟨_, rfl⟩
  have hi2 : 2 ≤ i := by omega
  have hi31 : i ≤ 2 ^ 31 := by omega
  rw [← hi] at hdi hb hr hlow
  rw [show n - m = i + 1 by omega] at ha hr
  have hJi := Jn_pos i w hw0 hw2.le
  have hJi' := hJi.ne'
  have hJim := Jn_pos (i - 1) w hw0 hw2.le
  have hJip := Jn_pos (i + 1) w hw0 hw2.le
  have hJn := Jn_pos n w hw0 hw2.le
  have hsum := J_sum w hw0 i (by omega)
  obtain ⟨hβ0, hβ1⟩ := βB_le m i (by omega)
  obtain ⟨hα0, hα1⟩ := αB_le m (by omega)
  obtain ⟨hT0, hT1⟩ := Tb_le m (by omega)
  have hB1 := abs_le.mp hb.2
  have ha1 := abs_le.mp ha.2
  have hσJip0 : 0 < σ * Jn (i + 1) w := by positivity
  have hσJi0 : 0 < σ * Jn i w := by positivity
  have hBlow : 1 / 4 ≤ value s.2.1.toBits := by nlinarith
  have hA0 : 0 < value s.1.toBits := by nlinarith
  -- the ratio `d`
  obtain ⟨d, hdd⟩ : ∃ d : ℝ, d = if i = 2 then 2 / 3 else 1 / 5 := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hdd]; split_ifs <;> norm_num
  have hd2 : d ≤ 5 := by rw [hdd]; split_ifs <;> norm_num
  have hdJ : Jn (i + 1) w ≤ d * Jn (i - 1) w := by
    rw [hdd]
    split_ifs with h
    · subst h; exact d_le w hw0 hw2.le 2 le_rfl
    · exact d_le5 w hw0 hw2.le i (by omega)
  -- the magnitude of `b dᵢ`
  have hJle : ∀ j : ℕ, 1 ≤ j → Jn j w ≤ 5 / 3 := by
    intro j hj
    have := Jn_le j hj w hw0.le hw2.le
    have h1 : (w / 2) ^ j ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have h2 : (1 : ℝ) ≤ j.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
    have h3 : (w / 2) ^ j / (j.factorial : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    linarith
  have hBm : value s.2.1.toBits * (2 * i / w) ≤ 2 ^ 1020 := by
    have hlw : 2 * (i : ℝ) / w = lam w i := by unfold lam; ring
    rw [hlw]
    have hlamJ : lam w i * Jn i w ≤ 10 / 3 := by
      rw [hsum]; linarith [hJle (i - 1) (by omega), hJle (i + 1) (by omega)]
    have hl0 : 0 ≤ lam w i := by unfold lam; positivity
    cases hsc : scale
    · have hσb := hsf hsc
      have hBu : value s.2.1.toBits ≤ σ * Jn i w * (1 + 1 / 2 ^ 18) := by nlinarith
      have h2 : value s.2.1.toBits * lam w i ≤ σ * Jn i w * (1 + 1 / 2 ^ 18) * lam w i :=
        mul_le_mul_of_nonneg_right hBu hl0
      have h3 : σ * Jn i w * (1 + 1 / 2 ^ 18) * lam w i = σ * (lam w i * Jn i w) * (1 + 1 / 2 ^ 18) := by
        ring
      have h4 : σ * (lam w i * Jn i w) ≤ 2 ^ 1017 * (10 / 3) :=
        mul_le_mul hσb hlamJ (by positivity) (by positivity)
      nlinarith
    · have hB2 := hst hsc
      have hl63 := lam_le w hw i (by omega)
      have := mul_le_mul hB2 hl63 hl0 (by positivity)
      linarith [show (2 : ℝ) ^ 333 * 2 ^ 63 ≤ 2 ^ 1020 by norm_num]
  -- the step itself
  have hE : |value s.2.1.toBits * Jn (i + 1) w - value s.1.toBits * Jn i w| ≤
      7 * 𝐮 * (value s.1.toBits * Jn i w) := by
    have : Er i = 7 * 𝐮 := by unfold Er; rw [if_neg (by omega)]
    rw [← this]; exact hr
  have hsum' : lam w i * Jn i w = Jn (i - 1) w + Jn (i + 1) w := hsum
  obtain ⟨hbf, hbe⟩ := bstep (a := s.1) (b := s.2.1) (di := s.2.2.2) (x := xa) i ha.1 hb.1 hdi hx
    hw hw2 (by omega) hi31 rfl rfl hA0 (le_trans (by norm_num) hBlow) hBm rfl hJi hJim hJip hsum'
    hdJ hd0 hd2 hE (by rw [hu]; positivity) (by rw [hu]; norm_num)
  have hK := K_bound d hd0 i hdd
  obtain ⟨Kb, hKb⟩ : ∃ Kb : ℝ, Kb = if i = 2 then 91 / 10 * 𝐮 else 49 / 10 * 𝐮 := ⟨_, rfl⟩
  rw [← hKb] at hK
  have hKb0 : 0 ≤ Kb := by rw [hKb]; split_ifs <;> positivity
  have hKb1 : Kb ≤ 91 / 10 * 𝐮 := by rw [hKb]; split_ifs <;> nlinarith
  have hT0' : 0 < value s.2.1.toBits * Jn (i - 1) w / Jn i w := by positivity
  have hbe2 : |value (s.2.1 * s.2.2.2 / xa - s.1).toBits - value s.2.1.toBits * Jn (i - 1) w / Jn i w| ≤
      Kb * (value s.2.1.toBits * Jn (i - 1) w / Jn i w) :=
    le_trans hbe (mul_le_mul_of_nonneg_right hK hT0'.le)
  -- the error of `b'` against `σ J_(i-1)`
  have hbE : |value (s.2.1 * s.2.2.2 / xa - s.1).toBits - σ * Jn (i - 1) w| ≤
      (Kb * (1 + βB m i) + βB m i) * (σ * Jn (i - 1) w) :=
    b_err hJi hJim hσJi0 rfl (by field_simp) hKb0 hβ0 hbe2 hb.2
  have hβnew : Kb * (1 + βB m i) + βB m i ≤ βB (m + 1) (i - 1) := by
    unfold βB
    rw [hKb, hu]
    have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hmb : (m : ℝ) ≤ 2 ^ 31 := by exact_mod_cast (show m ≤ 2 ^ 31 by omega)
    split_ifs with h1 h2 h3 <;> push_cast <;> (try omega) <;> nlinarith
  have hJdec := J_decr w hw0 hw2 i hi2
  have hdi2 := di_step i (by omega) hi31 hdi
  have hσJm0 : 0 < σ * Jn (i - 1) w := by positivity
  have hβn := βB_le (m + 1) (i - 1) (by omega)
  have hbE2 : |value (s.2.1 * s.2.2.2 / xa - s.1).toBits - σ * Jn (i - 1) w| ≤
      βB (m + 1) (i - 1) * (σ * Jn (i - 1) w) :=
    le_trans hbE (mul_le_mul_of_nonneg_right hβnew hσJm0.le)
  have hEr : Kb + 2 * (1 / 2 ^ 53) ≤ Er (i - 1) * (1 - 2 / 2 ^ 53) := by
    unfold Er
    rw [hKb, hu]
    split_ifs with h1 h2 h3 <;> (try omega) <;> norm_num
  unfold BInv
  rw [show n - 1 - (m + 1) = i - 1 by omega, show n - (m + 1) = i by omega]
  unfold bbody
  split_ifs with hsc
  · -- the code scales by `b'`
    have hscale : scale = true := by
      cases scale
      · simp at hsc
      · rfl
    have hgt : value (Float.ofBits 0x54B249AD2594C37D).toBits <
        value (s.2.1 * s.2.2.2 / xa - s.1).toBits := by
      have : (s.2.1 * s.2.2.2 / xa - s.1) > Float.ofBits 0x54B249AD2594C37D := by
        rw [hscale] at hsc; simpa using hsc
      exact (gt_c100 _ hbf).mp this
    obtain ⟨-, hc1, hc2⟩ := c100_facts
    set Bp := value (s.2.1 * s.2.2.2 / xa - s.1).toBits with hBp
    have hBp332 : 2 ^ 332 ≤ Bp := by linarith
    have hBp0 : 0 < Bp := lt_of_lt_of_le (by positivity) hBp332
    have hBpu : Bp ≤ (1 + βB (m + 1) (i - 1)) * (σ * Jn (i - 1) w) := by
      have := (abs_le.mp hbE2).2; nlinarith
    -- `σ J_(i-1) ≤ λ_i σ J_i ≤ 2^63 σ J_i`
    have hJr := J_ratio w hw0 hw2.le (i - 1)
    rw [show i - 1 + 1 = i by omega] at hJr
    have hlb := lam_le w hw i (by omega)
    have hJr2 : Jn (i - 1) w ≤ 2 ^ 63 * Jn i w := le_trans hJr (mul_le_mul_of_nonneg_right hlb hJi.le)
    have hYB : 1 / 2 ^ 64 ≤ σ * Jn i w / Bp := by
      rw [le_div_iff₀ hBp0]
      have : Bp ≤ 2 * (2 ^ 63 * (σ * Jn i w)) := by
        have h1 : σ * Jn (i - 1) w ≤ 2 ^ 63 * (σ * Jn i w) := by nlinarith
        nlinarith
      nlinarith
    have hdm := div_mag hb.1 hbf (show |value s.2.1.toBits| ≤ value s.2.1.toBits by
      rw [abs_of_pos (by linarith)]) hBp0 (show Bp ≤ |Bp| from le_abs_self _) (by
        rw [div_le_iff₀ hBp0]
        have : value s.2.1.toBits ≤ 2 ^ 1020 := by
          linarith [hst hscale, show (2 : ℝ) ^ 333 ≤ 2 ^ 1020 by norm_num]
        nlinarith)
    refine ⟨σ / Bp, by positivity, hdi2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- `b = 1`
      have hone := fapprox_one
      have hv1 : value (1.0 : Float).toBits = 1 := by have := abs_nonpos_iff.mp hone.2; linarith
      refine ⟨hone.1, ?_⟩
      rw [hv1, show σ / Bp * Jn (i - 1) w = σ * Jn (i - 1) w / Bp by ring]
      exact scale_b hBp0 hσJm0 hbE2
    · -- `a = b ⊘ b'`
      refine ⟨hdm.1, ?_⟩
      rw [show σ / Bp * Jn i w = σ * Jn i w / Bp by ring]
      exact scale_a hBp0 hσJi0 hβ0 (by linarith [show (1 : ℝ) / 2 ^ 18 ≤ 1 by norm_num]) hYB hdm.2 hb.2
        (by
          unfold αB βB
          rw [hu]
          have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
          have hmr2 : (m : ℝ) ≤ 2 ^ 31 := by exact_mod_cast (show m ≤ 2 ^ 31 by omega)
          split_ifs <;> push_cast <;> nlinarith)
    · -- the ratio
      have hv1 : value (1.0 : Float).toBits = 1 := by
        have := abs_nonpos_iff.mp fapprox_one.2; linarith
      rw [hv1]
      have hq : 1 / 2 ^ 70 ≤ value s.2.1.toBits / Bp := by
        have h1 := (abs_le.mp hb.2).1
        have h2 : σ * Jn i w * (1 - 1 / 2 ^ 18) ≤ value s.2.1.toBits := by nlinarith
        have h3 : 1 / 2 ^ 64 * (1 - 1 / 2 ^ 18) ≤ σ * Jn i w / Bp * (1 - 1 / 2 ^ 18) :=
          mul_le_mul_of_nonneg_right hYB (by norm_num)
        have h4 : σ * Jn i w / Bp * (1 - 1 / 2 ^ 18) ≤ value s.2.1.toBits / Bp := by
          rw [show σ * Jn i w / Bp * (1 - 1 / 2 ^ 18) = σ * Jn i w * (1 - 1 / 2 ^ 18) / Bp by ring]
          exact div_le_div_of_nonneg_right h2 hBp0.le
        have : (1 : ℝ) / 2 ^ 70 ≤ 1 / 2 ^ 64 * (1 - 1 / 2 ^ 18) := by norm_num
        linarith
      exact scale_ratio hBp0 hJi hJim (by linarith) rfl hKb0 hbe2 hq hdm.2 hEr
    · exact (div_mag htf hbf (le_refl _) hBp0 (le_abs_self _) (hAm htf hBp0 hBp332)).1
    · have hdt := div_mag htf hbf (le_refl _) hBp0 (le_abs_self _) (hAm htf hBp0 hBp332)
      rw [show σ / Bp * Jn n w = σ * Jn n w / Bp by ring]
      have h := scale_t hBp332 (by positivity) hT0 hT1 ht hdt.2
      have e : Tb (m + 1) = Tb m + 101 / 100 * (1 / 2 ^ 53) := by unfold Tb; push_cast; rw [hu]; ring
      rw [e]
      exact h
    · rw [show σ / Bp * Jn (i - 1) w = σ * Jn (i - 1) w / Bp by ring, le_div_iff₀ hBp0]
      nlinarith
    · intro h; rw [hscale] at h; exact absurd h (by decide)
    · intro _
      have hv1 : value (1.0 : Float).toBits = 1 := by
        have := abs_nonpos_iff.mp fapprox_one.2; linarith
      show value (1.0 : Float).toBits ≤ 2 ^ 333
      rw [hv1]; norm_num
  · -- no scaling
    refine ⟨σ, hσ, hdi2, ⟨hbf, hbE2⟩, fmono hb ?_, ?_, htf, ?_, ?_, hsf, ?_⟩
    · apply mul_le_mul_of_nonneg_right _ hσJi0.le
      unfold αB βB
      rw [hu]
      have hmr : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      split_ifs <;> push_cast <;> nlinarith
    · -- the ratio
      have hEr' : Kb ≤ Er (i - 1) := by
        unfold Er; rw [hKb, hu]; split_ifs with h1 h2 h3 <;> (try omega) <;> norm_num
      rw [show value (s.2.1 * s.2.2.2 / xa - s.1).toBits * Jn i w - value s.2.1.toBits * Jn (i - 1) w =
        Jn i w * (value (s.2.1 * s.2.2.2 / xa - s.1).toBits -
          value s.2.1.toBits * Jn (i - 1) w / Jn i w) by field_simp, abs_mul, abs_of_pos hJi]
      have h1 := mul_le_mul_of_nonneg_left hbe2 hJi.le
      have e : Jn i w * (Kb * (value s.2.1.toBits * Jn (i - 1) w / Jn i w)) =
          Kb * (value s.2.1.toBits * Jn (i - 1) w) := by field_simp
      have h2 : Kb * (value s.2.1.toBits * Jn (i - 1) w) ≤ Er (i - 1) * (value s.2.1.toBits * Jn (i - 1) w) :=
        mul_le_mul_of_nonneg_right hEr' (by positivity)
      linarith
    · have : Tb m ≤ Tb (m + 1) := by unfold Tb; push_cast; nlinarith
      have := mul_le_mul_of_nonneg_right this (show 0 ≤ σ * Jn n w by positivity)
      linarith
    · nlinarith
    · intro hs1
      have hng : ¬ (s.2.1 * s.2.2.2 / xa - s.1) > Float.ofBits 0x54B249AD2594C37D := by
        intro hc; apply hsc; rw [hs1]; simpa using hc
      rw [gt_c100 _ hbf] at hng
      push Not at hng
      obtain ⟨-, -, hc2⟩ := c100_facts
      show value (s.2.1 * s.2.2.2 / xa - s.1).toBits ≤ 2 ^ 333
      linarith

#print axioms int_sub_exact
#print axioms di_step
#print axioms binv_zero
#print axioms binv_step

end Verified.Examples.BesselMillerBack
