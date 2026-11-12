import Demos.Conjunction.Program
import Demos.Conjunction.Model
import Demos.Conjunction.Gaussian
import Library.Numerics.Interval.Proof
import Library.Numerics.Float64.Exp.ExpTheorem
import Library.Numerics.Float64.Erf.ErfOdd
import LeanExe.Dialect.Lemmas

/-!
Soundness of the conjunction program.  `pc_enclosure` states that an accepted result of `pc`
contains the probability of collision `Model.pc` of the real values of the inputs and has an upper
endpoint of at most 1, and `assess_sound` states what each verdict of `assess` implies.  The proof
follows the program: each interval function contains the real function it computes, each panel
contains the integral of `Model.core` over it, the loop adds the panels from `-r` to `r`, and the
clamp to `[0, 1]` keeps `Model.pc`, which `Model.pc_nonneg` and `Gaussian.pc_le_one` place there.
-/

namespace Demos.Conjunction

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

/-! ### Constants -/

theorem zero_bits : (0.0 : Float).toBits = 0 := by decide +kernel
theorem one_bits : (1.0 : Float).toBits = 0x3FF0000000000000 := by decide +kernel
theorem two_bits : (2.0 : Float).toBits = 0x4000000000000000 := by decide +kernel

theorem lit_zero : Finite (0.0 : Float).toBits ∧ value (0.0 : Float).toBits = 0 := by
  have hs : Wasm.IEEE64.scaledValue 0 = 0 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [zero_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [zero_bits, value, hs]; norm_num

theorem lit_one : Finite (1.0 : Float).toBits ∧ value (1.0 : Float).toBits = 1 := by
  have hs : Wasm.IEEE64.scaledValue 0x3FF0000000000000 = 2 ^ 1074 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [one_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [one_bits, value, hs]; push_cast; norm_num

theorem lit_two : Finite (2.0 : Float).toBits ∧ value (2.0 : Float).toBits = 2 := by
  have hs : Wasm.IEEE64.scaledValue 0x4000000000000000 = 2 ^ 1075 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [two_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [two_bits, value, hs]; push_cast; norm_num

theorem point_lit {x : Float} {q : ℝ} (hx : Finite x.toBits ∧ value x.toBits = q)
    (h : (point x).status = 0) : Contains (point x) q := by
  have := (point_sound h).2
  rwa [hx.2] at this

/-- The interval `twoPi` contains `2π`. -/
theorem twoPi_sound : Contains twoPi (2 * Real.pi) := by
  have hlo : (Float.ofBits 0x401921FB54442D18).toBits = 0x401921FB54442D18 :=
    toBits_ofBits_of_finite (by decide)
  have hhi : (Float.ofBits 0x401921FB54442D19).toBits = 0x401921FB54442D19 :=
    toBits_ofBits_of_finite (by decide)
  have slo : Wasm.IEEE64.scaledValue 0x401921FB54442D18 = 7074237752028440 * 2 ^ 1024 := by
    decide +kernel
  have shi : Wasm.IEEE64.scaledValue 0x401921FB54442D19 = 7074237752028441 * 2 ^ 1024 := by
    decide +kernel
  have vlo : value (0x401921FB54442D18 : UInt64) = 7074237752028440 / 2 ^ 50 := by
    simp only [value, slo]; push_cast; norm_num
  have vhi : value (0x401921FB54442D19 : UInt64) = 7074237752028441 / 2 ^ 50 := by
    simp only [value, shi]; push_cast; norm_num
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · show Finite (Float.ofBits 0x401921FB54442D18).toBits
    rw [hlo]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · show Finite (Float.ofBits 0x401921FB54442D19).toBits
    rw [hhi]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · show value (Float.ofBits 0x401921FB54442D18).toBits ≤ 2 * Real.pi
    rw [hlo, vlo]
    norm_num at h1 ⊢
    linarith
  · show 2 * Real.pi ≤ value (Float.ofBits 0x401921FB54442D19).toBits
    rw [hhi, vhi]
    norm_num at h2 ⊢
    linarith

/-! ### Library functions -/

theorem expWith_within (x : Float) (hx : Finite x.toBits) :
    F64SignedRounding.WithinSteps 1 (Real.exp (value x.toBits))
      (Exp.expWith Exp.expTable x).toBits := by
  obtain ⟨h1, h2, h3⟩ := Exp.ExpTheorem.exp_one_step x hx
  exact F64SignedRounding.within_of_nonneg 1 _ (Real.exp_pos _).le _ h1 h2 h3

theorem sq_sound {a : Interval} (h : (sq a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (sq a) (x ^ 2) := by
  simp only [sq] at h ⊢
  obtain ⟨h1, -, hm⟩ := mul_sound h
  obtain ⟨h2, ha⟩ := abs_sound h1
  refine ⟨h2, fun x hx => ?_⟩
  have hc := hm _ _ (ha x hx) (ha x hx)
  rwa [abs_mul_abs_self, ← pow_two] at hc

theorem expI_sound {a : Interval} (h : (expI Exp.expTable a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (expI Exp.expTable a) (Real.exp x) := by
  unfold expI at h ⊢
  exact increasing_sound h (Real.exp_monotone.monotoneOn _) (fun hf => expWith_within _ hf)
    (fun hf => expWith_within _ hf)

theorem erfI_sound {a : Interval} (h : (erfI Exp.expTable a).status = 0) :
    a.status = 0 ∧ ∀ x, Contains a x → Contains (erfI Exp.expTable a) (RealErf.erf x) := by
  unfold erfI at h ⊢
  exact increasing_sound h (RealErf.erf_strictMono.monotone.monotoneOn _)
    (fun hf => Erf.ErfOdd.erfWith_within_one _ hf) (fun hf => Erf.ErfOdd.erfWith_within_one _ hf)

theorem erf_sum_nonneg {a b : ℝ} (h : 0 ≤ a + b) : 0 ≤ RealErf.erf a + RealErf.erf b := by
  have hm := RealErf.erf_strictMono.monotone (show -b ≤ a by linarith)
  rw [RealErf.erf_neg] at hm
  linarith

theorem erf_sum_le_two (a b : ℝ) : RealErf.erf a + RealErf.erf b ≤ 2 := by
  linarith [RealErf.erf_lt_one a, RealErf.erf_lt_one b]

/-! ### The setup -/

/-- Each accepted field of a setup contains its real quantity, for the radius `r` and the real
mean and covariance. -/
structure SetupSound (st : Setup) (r : Float) (m1 m2 c11 c12 c22 : ℝ) : Prop where
  m1 : st.m1.status = 0 → Contains st.m1 m1
  m2 : st.m2.status = 0 → Contains st.m2 m2
  twoC11 : st.twoC11.status = 0 → Contains st.twoC11 (2 * c11)
  rho : st.rho.status = 0 → Contains st.rho (c12 / c11)
  k : st.k.status = 0 →
    0 ≤ Model.condVar c11 c12 c22 ∧ Contains st.k (Model.scaleK c11 c12 c22)
  r2 : st.r2.status = 0 → Finite r.toBits ∧ Contains st.r2 (value r.toBits ^ 2)

theorem setup_sound (m1 m2 c11 c12 c22 r : Float) :
    SetupSound (setup m1 m2 c11 c12 c22 r) r (value m1.toBits) (value m2.toBits)
      (value c11.toBits) (value c12.toBits) (value c22.toBits) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact (point_sound (x := m1) h).2
  · intro h
    exact (point_sound (x := m2) h).2
  · intro h
    have h' : (mul (point 2.0) (point c11)).status = 0 := h
    obtain ⟨s1, s2, hm⟩ := mul_sound h'
    have hc := hm _ _ (point_lit lit_two s1) (point_sound s2).2
    exact hc
  · intro h
    have h' : (div (point c12) (point c11)).status = 0 := h
    obtain ⟨s1, s2, hd⟩ := div_sound h'
    exact (hd _ _ (point_sound s1).2 (point_sound s2).2).2
  · intro h
    have h' : (mul (sqrt (sub (point c22) (div (sq (point c12)) (point c11))))
        (sqrt (point 2.0))).status = 0 := h
    obtain ⟨s1, s2, hm⟩ := mul_sound h'
    obtain ⟨s3, hq⟩ := sqrt_sound s1
    obtain ⟨s4, hq2⟩ := sqrt_sound s2
    obtain ⟨s5, s6, hs⟩ := sub_sound s3
    obtain ⟨s7, s8, hd⟩ := div_sound s6
    obtain ⟨s9, hsq⟩ := sq_sound s7
    have c1 := hs _ _ (point_sound s5).2
      (hd _ _ (hsq _ (point_sound s9).2) (point_sound s8).2).2
    obtain ⟨n1, c2⟩ := hq _ c1
    obtain ⟨-, c3⟩ := hq2 _ (point_lit lit_two s4)
    exact ⟨n1, hm _ _ c2 c3⟩
  · intro h
    have h' : (sq (point r)).status = 0 := h
    obtain ⟨s1, hsq⟩ := sq_sound h'
    obtain ⟨f1, c1⟩ := point_sound s1
    exact ⟨f1, hsq _ c1⟩

/-! ### The integrand on a panel -/

section Panel

variable {st : Setup} {r : Float} {m1 m2 c11 c12 c22 : ℝ}

theorem gaussI_sound (S : SetupSound st r m1 m2 c11 c12 c22) (hc : 0 < c11) {X : Interval}
    (h : (gaussI Exp.expTable st X).status = 0) :
    X.status = 0 ∧ ∀ x, Contains X x →
      Contains (gaussI Exp.expTable st X) (Real.exp (-(x - m1) ^ 2 / (2 * c11))) := by
  unfold gaussI at h ⊢
  obtain ⟨s1, hcl⟩ := clamp_sound h
  obtain ⟨s2, he⟩ := expI_sound s1
  obtain ⟨s3, hn⟩ := neg_sound s2
  obtain ⟨s4, s5, hd⟩ := div_sound s3
  obtain ⟨s6, hsq⟩ := sq_sound s4
  obtain ⟨s7, s8, hs⟩ := sub_sound s6
  refine ⟨s7, fun x hx => ?_⟩
  have c1 := he _ (hn _ (hd _ _ (hsq _ (hs _ _ hx (S.m1 s8))) (S.twoC11 s5)).2)
  have hneg : -((x - m1) ^ 2 / (2 * c11)) ≤ 0 :=
    neg_nonpos.mpr (div_nonneg (sq_nonneg _) (by linarith))
  have c2 := hcl _ c1 (by rw [lit_zero.2]; exact (Real.exp_pos _).le)
    (by rw [lit_one.2]; exact Real.exp_le_one_iff.mpr hneg)
  rwa [← neg_div] at c2

theorem chordI_sound (S : SetupSound st r m1 m2 c11 c12 c22) {X : Interval}
    (h : (chordI st X).status = 0) :
    X.status = 0 ∧ Finite r.toBits ∧ ∀ x, Contains X x → x ^ 2 ≤ value r.toBits ^ 2 →
      Contains (chordI st X) (Real.sqrt (value r.toBits ^ 2 - x ^ 2)) := by
  unfold chordI at h ⊢
  obtain ⟨s1, hq⟩ := sqrt_sound h
  obtain ⟨s2, hcl⟩ := clamp_sound s1
  obtain ⟨s3, s4, hs⟩ := sub_sound s2
  obtain ⟨s5, hsq⟩ := sq_sound s4
  obtain ⟨fr, cr⟩ := S.r2 s3
  refine ⟨s5, fr, fun x hx hx2 => ?_⟩
  have c1 := hs _ _ cr (hsq _ hx)
  have c2 := hcl _ c1 (by rw [lit_zero.2]; linarith)
    (by linarith [cr.2.2.2.2, sq_nonneg x])
  exact (hq _ c2).2

theorem meanI_sound (S : SetupSound st r m1 m2 c11 c12 c22) {X : Interval}
    (h : (meanI st X).status = 0) :
    ∀ x, Contains X x → Contains (meanI st X) (Model.condMean m1 m2 c11 c12 x) := by
  unfold meanI at h ⊢
  obtain ⟨s1, s2, ha⟩ := add_sound h
  obtain ⟨s3, s4, hm⟩ := mul_sound s2
  obtain ⟨s5, s6, hs⟩ := sub_sound s4
  intro x hx
  exact ha _ _ (S.m2 s1) (hm _ _ (S.rho s3) (hs _ _ hx (S.m1 s6)))

theorem erfSumI_sound (S : SetupSound st r m1 m2 c11 c12 c22) {X : Interval}
    (h : (erfSumI Exp.expTable st X).status = 0) :
    X.status = 0 ∧ Finite r.toBits ∧ ∀ x, Contains X x → x ^ 2 ≤ value r.toBits ^ 2 →
      0 < Model.condVar c11 c12 c22 ∧
      Contains (erfSumI Exp.expTable st X)
        (RealErf.erf ((Real.sqrt (value r.toBits ^ 2 - x ^ 2) -
            Model.condMean m1 m2 c11 c12 x) / Model.scaleK c11 c12 c22) +
          RealErf.erf ((Real.sqrt (value r.toBits ^ 2 - x ^ 2) +
            Model.condMean m1 m2 c11 c12 x) / Model.scaleK c11 c12 c22)) := by
  simp only [erfSumI] at h ⊢
  obtain ⟨s1, hcl⟩ := clamp_sound h
  obtain ⟨s2, s3, ha⟩ := add_sound s1
  obtain ⟨s4, he1⟩ := erfI_sound s2
  obtain ⟨s5, he2⟩ := erfI_sound s3
  obtain ⟨s6, s7, hd1⟩ := div_sound s4
  obtain ⟨s8, -, hd2⟩ := div_sound s5
  obtain ⟨s9, s10, hsub⟩ := sub_sound s6
  obtain ⟨-, -, hadd⟩ := add_sound s8
  obtain ⟨sX, fr, hch⟩ := chordI_sound S s9
  have hmu := meanI_sound S s10
  obtain ⟨hv0, ck⟩ := S.k s7
  refine ⟨sX, fr, fun x hx hx2 => ?_⟩
  have ch := hch x hx hx2
  have cm := hmu x hx
  obtain ⟨hk0, c1⟩ := hd1 _ _ (hsub _ _ ch cm) ck
  obtain ⟨-, c2⟩ := hd2 _ _ (hadd _ _ ch cm) ck
  have hkpos : 0 < Model.scaleK c11 c12 c22 :=
    lt_of_le_of_ne (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Ne.symm hk0)
  have hvpos : 0 < Model.condVar c11 c12 c22 := by
    rcases hv0.eq_or_lt with hz | hz
    · exfalso
      apply hk0
      unfold Model.scaleK
      rw [← hz, Real.sqrt_zero, zero_mul]
    · exact hz
  have c3 := ha _ _ (he1 _ c1) (he2 _ c2)
  refine ⟨hvpos, hcl _ c3 ?_ ?_⟩
  · rw [lit_zero.2]
    apply erf_sum_nonneg
    rw [← add_div]
    exact div_nonneg (by linarith [Real.sqrt_nonneg (value r.toBits ^ 2 - x ^ 2)]) hkpos.le
  · rw [lit_two.2]
    exact erf_sum_le_two _ _

theorem panelCore_sound (S : SetupSound st r m1 m2 c11 c12 c22) (hc : 0 < c11) {X : Interval}
    (h : (panelCore Exp.expTable st X).status = 0) :
    X.status = 0 ∧ Finite r.toBits ∧ ∀ x, Contains X x → x ^ 2 ≤ value r.toBits ^ 2 →
      0 < Model.condVar c11 c12 c22 ∧
      Contains (panelCore Exp.expTable st X) (Model.core m1 m2 c11 c12 c22 (value r.toBits) x) := by
  unfold panelCore at h ⊢
  obtain ⟨s1, s2, hm⟩ := mul_sound h
  obtain ⟨sX, hg⟩ := gaussI_sound S hc s1
  obtain ⟨-, fr, he⟩ := erfSumI_sound S s2
  refine ⟨sX, fr, fun x hx hx2 => ?_⟩
  obtain ⟨hv, ce⟩ := he x hx hx2
  exact ⟨hv, hm _ _ (hg x hx) ce⟩

/-- An accepted panel contains the integral of `Model.core` over it. -/
theorem panel_sound (S : SetupSound st r m1 m2 c11 c12 c22) (hc : 0 < c11) {a b : Float}
    (hab : Finite r.toBits →
      -value r.toBits ≤ value a.toBits ∧ value b.toBits ≤ value r.toBits)
    (h : (panel Exp.expTable st a b).status = 0) :
    Finite r.toBits ∧ 0 < Model.condVar c11 c12 c22 ∧
      Contains (panel Exp.expTable st a b)
        (∫ x in (value a.toBits)..(value b.toBits),
          Model.core m1 m2 c11 c12 c22 (value r.toBits) x) := by
  unfold panel at h ⊢
  obtain ⟨s1, s2, hm⟩ := mul_sound h
  obtain ⟨s3, s4, hs⟩ := sub_sound s1
  obtain ⟨sX, fr, hp⟩ := panelCore_sound S hc s2
  obtain ⟨fa, fb, hle, hmk⟩ := make_sound sX
  obtain ⟨ha, hb⟩ := hab fr
  have hx2 : ∀ x ∈ Set.Icc (value a.toBits) (value b.toBits), x ^ 2 ≤ value r.toBits ^ 2 :=
    fun x hx => sq_le_sq' (ha.trans hx.1) (hx.2.trans hb)
  have hin : ∀ x ∈ Set.Icc (value a.toBits) (value b.toBits),
      Contains (panelCore Exp.expTable st (make a b))
        (Model.core m1 m2 c11 c12 c22 (value r.toBits) x) :=
    fun x hx => (hp x (hmk x hx.1 hx.2) (hx2 x hx)).2
  have hv := (hp _ (hmk _ le_rfl hle) (hx2 _ ⟨le_rfl, hle⟩)).1
  have h0 := hin _ ⟨le_rfl, hle⟩
  obtain ⟨y, hy1, hy2, hint⟩ := Model.integral_eq_width_mul hle
    ((Model.continuous_core m1 m2 c11 c12 c22 (value r.toBits)).intervalIntegrable _ _)
    (fun x hx => ⟨(hin x hx).2.2.2.1, (hin x hx).2.2.2.2⟩)
  have cy : Contains (panelCore Exp.expTable st (make a b)) y :=
    ⟨h0.1, h0.2.1, h0.2.2.1, hy1, hy2⟩
  have cw := hs _ _ (point_sound s3).2 (point_sound s4).2
  refine ⟨fr, hv, ?_⟩
  rw [hint]
  exact hm _ _ cw cy

end Panel

/-! ### Partition points -/

theorem node_bounds (r : Float) (n i : UInt64) (hr : Finite r.toBits)
    (h0 : 0 ≤ value r.toBits) :
    Finite (node r n i).toBits ∧ -value r.toBits ≤ value (node r n i).toBits ∧
      value (node r n i).toBits ≤ value r.toBits := by
  obtain ⟨fn, vn⟩ := neg_value hr
  unfold node
  by_cases h1 : (i == 0) = true
  · simp only [h1, ite_true]
    exact ⟨fn, by rw [vn], by rw [vn]; linarith⟩
  · by_cases h2 : n ≤ i
    · simp only [h1, h2, Bool.false_eq_true, ite_false, ite_true]
      exact ⟨hr, by linarith, le_rfl⟩
    · simp only [h1, h2, Bool.false_eq_true, ite_false]
      split_ifs with h3 h4 h5
      · have ft := (finite_iff _).mp h3
        have h6 := (le_iff_value fn ft).mp h4
        rw [vn] at h6
        exact ⟨ft, h6, (le_iff_value ft hr).mp h5⟩
      · exact ⟨hr, by linarith, le_rfl⟩
      · exact ⟨hr, by linarith, le_rfl⟩
      · exact ⟨hr, by linarith, le_rfl⟩

theorem node_zero (r : Float) (n : UInt64) : node r n 0 = -r := by
  simp [node]

theorem node_last (r : Float) (n : UInt64) (hn : 1 ≤ n) : node r n n = r := by
  have h1 : ¬ (n == 0) = true := by
    intro h
    rw [beq_iff_eq.mp h] at hn
    exact absurd hn (by decide)
  simp [node, h1]

/-! ### The sum of the panels -/

/-- The sum of the panels contains the integral of `Model.core` over `[-r, r]` for every setup
whose fields contain the quantities of the real mean and covariance. -/
theorem panels_sound_of {st : Setup} {r : Float} {n : UInt64} {m1 m2 c11 c12 c22 : ℝ}
    (S : SetupSound st r m1 m2 c11 c12 c22) (hc : 0 < c11)
    (hr : Finite r.toBits → 0 < value r.toBits) (hn : 1 ≤ n)
    (h : (panels Exp.expTable st r n).status = 0) :
    Finite r.toBits ∧ 0 < Model.condVar c11 c12 c22 ∧
      Contains (panels Exp.expTable st r n)
        (∫ x in (-value r.toBits)..(value r.toBits),
          Model.core m1 m2 c11 c12 c22 (value r.toBits) x) := by
  set F := Model.core m1 m2 c11 c12 c22 (value r.toBits) with hF
  have hFi : ∀ a b : ℝ, IntervalIntegrable F MeasureTheory.volume a b := fun a b =>
    (Model.continuous_core _ _ _ _ _ _).intervalIntegrable a b
  have key := LeanExe.Dialect.loop_induction (n := n) (init := point 0.0)
    (f := fun i acc => add acc (panel Exp.expTable st (node r n i) (node r n (i + 1))))
    (fun k acc => acc.status = 0 →
      (0 < k → Finite r.toBits ∧ 0 < Model.condVar c11 c12 c22) ∧
      Contains acc (∫ x in (value (node r n (UInt64.ofNat 0)).toBits)..
        (value (node r n (UInt64.ofNat k)).toBits), F x))
    (by
      intro hs
      refine ⟨fun hk => absurd hk (lt_irrefl 0), ?_⟩
      rw [intervalIntegral.integral_same]
      exact point_lit lit_zero hs)
    (by
      intro k acc hk ih hs
      obtain ⟨s1, s2, ha⟩ := add_sound hs
      obtain ⟨-, c1⟩ := ih s1
      have e : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
        rw [UInt64.ofNat_add]
        rfl
      rw [e] at s2 ha ⊢
      obtain ⟨fr, hv, c2⟩ := panel_sound S hc
        (fun fr => ⟨(node_bounds r n _ fr (hr fr).le).2.1,
          (node_bounds r n _ fr (hr fr).le).2.2⟩) s2
      refine ⟨fun _ => ⟨fr, hv⟩, ?_⟩
      have hsum := ha _ _ c1 c2
      rwa [intervalIntegral.integral_add_adjacent_intervals (hFi _ _) (hFi _ _)] at hsum)
  have hfin := key h
  obtain ⟨fr, hv⟩ := hfin.1 (by
    have : 1 ≤ n.toNat := by
      have := UInt64.le_iff_toNat_le.mp hn
      simpa using this
    omega)
  refine ⟨fr, hv, ?_⟩
  have hl : node r n (UInt64.ofNat n.toNat) = r := by
    rw [UInt64.ofNat_toNat]
    exact node_last r n hn
  have hz : node r n (UInt64.ofNat 0) = -r := node_zero r n
  have c := hfin.2
  rwa [hl, hz, (neg_value fr).2] at c

theorem panels_sound {m1 m2 c11 c12 c22 r : Float} {n : UInt64} (hc : 0 < value c11.toBits)
    (hr : Finite r.toBits → 0 < value r.toBits) (hn : 1 ≤ n)
    (h : (panels Exp.expTable (setup m1 m2 c11 c12 c22 r) r n).status = 0) :
    Finite r.toBits ∧
      0 < Model.condVar (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
      Contains (panels Exp.expTable (setup m1 m2 c11 c12 c22 r) r n)
        (∫ x in (-value r.toBits)..(value r.toBits),
          Model.core (value m1.toBits) (value m2.toBits) (value c11.toBits) (value c12.toBits)
            (value c22.toBits) (value r.toBits) x) :=
  panels_sound_of (setup_sound m1 m2 c11 c12 c22 r) hc hr hn h

/-! ### The interval and the verdict -/

/-- An accepted clamp's upper endpoint is at most the clamp's upper bound. -/
theorem clamp_hi_le {a : Interval} {lo hi : Float} (h : (clamp a lo hi).status = 0)
    (fa : Finite a.hi.toBits) (fh : Finite hi.toBits) :
    value (clamp a lo hi).hi.toBits ≤ value hi.toBits := by
  unfold clamp at h ⊢
  by_cases hc : (a.status == 0 && finite lo && finite hi) = true
  · simp only [hc, ite_true]
    show value (fmin a.hi hi).toBits ≤ value hi.toBits
    rw [(fmin_value fa fh).2]
    exact min_le_right _ _
  · simp only [hc, Bool.false_eq_true, ite_false] at h
    exact absurd h (by decide)

/-- An accepted result of `pc` contains the probability of collision of the real values of the
inputs, whose covariance is positive definite and whose radius is positive, and its upper endpoint
is at most 1. -/
theorem pc_enclosure {m1 m2 c11 c12 c22 r : Float} {n : UInt64}
    (h : (pc m1 m2 c11 c12 c22 r n).status = 0) :
    0 < value c11.toBits ∧
      0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
      0 < value r.toBits ∧
      Contains (pc m1 m2 c11 c12 c22 r n)
        (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits) (value c12.toBits)
          (value c22.toBits) (value r.toBits)) ∧
      value (pc m1 m2 c11 c12 c22 r n).hi.toBits ≤ 1 := by
  unfold pc pcWith at h ⊢
  by_cases g1 : (0.0 : Float) < c11
  · by_cases g2 : (0.0 : Float) < r
    · by_cases g3 : 1 ≤ n
      · by_cases g4 : n ≤ 1048576
        · simp only [g1, g2, g3, g4, ite_true] at h ⊢
          obtain ⟨s0, hcl⟩ := clamp_sound h
          obtain ⟨s1, s2, hm⟩ := mul_sound s0
          obtain ⟨s3, s4, hd⟩ := div_sound s1
          obtain ⟨s5, s6, hm2⟩ := mul_sound s4
          obtain ⟨s7, hq⟩ := sqrt_sound s6
          obtain ⟨-, s8, hm3⟩ := mul_sound s7
          obtain ⟨fc, cc⟩ := point_sound s8
          have hc : 0 < value c11.toBits := by
            have := (lt_iff_value lit_zero.1 fc).mp g1
            rwa [lit_zero.2] at this
          have hr : Finite r.toBits → 0 < value r.toBits := fun fr => by
            have := (lt_iff_value lit_zero.1 fr).mp g2
            rwa [lit_zero.2] at this
          obtain ⟨fr, hv, cp⟩ := panels_sound hc hr g3 s2
          have hdet : 0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) := by
            have e : Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) =
                value c11.toBits *
                  Model.condVar (value c11.toBits) (value c12.toBits) (value c22.toBits) := by
              unfold Model.det Model.condVar
              field_simp
            rw [e]
            exact mul_pos hc hv
          have c1 := (hq _ (hm3 _ _ twoPi_sound cc)).2
          have c2 := (hd _ _ (point_lit lit_one s3) (hm2 _ _ (point_lit lit_two s5) c1)).2
          have c3 := hm _ _ c2 cp
          rw [one_div, ← Model.pc_eq _ _ _ _ _ _ hc hdet (hr fr).le] at c3
          have hle := Gaussian.pc_le_one (value m1.toBits) (value m2.toBits) _ _ _
            (value r.toBits) hc hdet
          have hhi := clamp_hi_le h c3.2.2.1 lit_one.1
          rw [lit_one.2] at hhi
          exact ⟨hc, hdet, hr fr,
            hcl _ c3 (by rw [lit_zero.2]; exact Model.pc_nonneg _ _ _ _ _ _)
              (by rw [lit_one.2]; exact hle), hhi⟩
        · simp only [g1, g2, g3, g4, ite_true, ite_false] at h
          exact absurd h (by decide)
      · simp only [g1, g2, g3, ite_true, ite_false] at h
        exact absurd h (by decide)
    · simp only [g1, g2, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [g1, ite_false] at h
    exact absurd h (by decide)

/-- An accepted assessment holds the interval of `pc`.  Verdict 1 implies that the probability of
collision is below the threshold, and verdict 2 that it is at least the threshold. -/
theorem assess_sound {m1 m2 c11 c12 c22 r t : Float} {n : UInt64}
    (h : (assess m1 m2 c11 c12 c22 r t n).status = 0) :
    (pc m1 m2 c11 c12 c22 r n).status = 0 ∧
      (assess m1 m2 c11 c12 c22 r t n).lo = (pc m1 m2 c11 c12 c22 r n).lo ∧
      (assess m1 m2 c11 c12 c22 r t n).hi = (pc m1 m2 c11 c12 c22 r n).hi ∧
      ((assess m1 m2 c11 c12 c22 r t n).verdict = 1 →
        Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits) (value c12.toBits)
          (value c22.toBits) (value r.toBits) < value t.toBits) ∧
      ((assess m1 m2 c11 c12 c22 r t n).verdict = 2 →
        value t.toBits ≤ Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits)
          (value c12.toBits) (value c22.toBits) (value r.toBits)) := by
  have hpc : pcWith Exp.expTable m1 m2 c11 c12 c22 r n = pc m1 m2 c11 c12 c22 r n := rfl
  simp only [assess, assessWith, hpc] at h ⊢
  by_cases g : ((pc m1 m2 c11 c12 c22 r n).status == 0 && finite t) = true
  · simp only [g, ite_true] at h ⊢
    simp only [Bool.and_eq_true, beq_iff_eq, finite_iff] at g
    obtain ⟨gs, ft⟩ := g
    obtain ⟨-, -, -, ⟨-, fl, fh, hlo, hhi⟩, -⟩ := pc_enclosure gs
    by_cases g1 : (pc m1 m2 c11 c12 c22 r n).hi < t
    · simp only [g1, ite_true]
      exact ⟨gs, trivial, trivial, fun _ => lt_of_le_of_lt hhi ((lt_iff_value fh ft).mp g1),
        fun hv => absurd hv (by decide)⟩
    · by_cases g2 : t ≤ (pc m1 m2 c11 c12 c22 r n).lo
      · simp only [g1, g2, ite_true, ite_false]
        exact ⟨gs, trivial, trivial, fun hv => absurd hv (by decide),
          fun _ => ((le_iff_value ft fl).mp g2).trans hlo⟩
      · simp only [g1, g2, ite_false]
        exact ⟨gs, trivial, trivial, fun hv => absurd hv (by decide), fun hv => absurd hv (by decide)⟩
  · simp only [g, ite_false, Bool.false_eq_true] at h
    exact absurd h (by decide)

#print axioms pc_enclosure
#print axioms assess_sound

end Demos.Conjunction
