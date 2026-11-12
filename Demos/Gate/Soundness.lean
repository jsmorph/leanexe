import Demos.Gate.Program
import Demos.Gate.Model
import Demos.Conjunction.AccuracySoundness
import Library.Numerics.Interval.FunctionsProof
import Library.Numerics.Float64.Erfc.ErfcTheorem

/-!
Soundness of the chi-square programs.  `tail_sound` and `cdf_sound` state that an accepted
result of `tail` or `cdf` contains `Model.tail` or `Model.cdf` at the real value of `x`, and
`quantile_sound` that an accepted result of `quantile` holds the quantile at `p`.  The proof of
the tail follows the program: each interval contains its real quantity, the loop of `terms` keeps
a partial sum of the closed form and its next term, and `Model.tail_closed` equates the closed
form with the tail.  The quantile's first bisection keeps a lower end whose distribution function
an enclosure shows below `p`, the second an upper end whose distribution function an enclosure
shows at least `p`, and `Model.quantileIn_of` gives the quantile between them.
-/

namespace Demos.Gate

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

/-- The functions of the program with the module's tables. -/
abbrev erfcT (a : Interval) : Interval :=
  erfcI Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable Erfc.asymAccTable
    Erfc.expAccTable Erfc.excTable a

abbrev coreT (k : UInt64) (x : Float) : Interval :=
  tailCore Exp.expTable Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable
    Erfc.asymAccTable Erfc.expAccTable Erfc.excTable k x

abbrev cdfAtT (k : UInt64) (x : Float) : Interval :=
  cdfAt Exp.expTable Erfc.fastTable Erfc.accTable Erfc.expTable Erfc.asymTable
    Erfc.asymAccTable Erfc.expAccTable Erfc.excTable k x

/-! ### Enclosures -/

theorem encloses_point (x : Float) : Encloses (point x) (value x.toBits) :=
  fun h => (point_sound h).2

theorem encloses_lit {x : Float} {q : ℝ} (hx : Finite x.toBits ∧ value x.toBits = q) :
    Encloses (point x) q :=
  fun h => Conjunction.point_lit hx h

theorem encloses_clamp {a : Interval} {x : ℝ} (lo hi : Float) (ha : Encloses a x)
    (hlo : value lo.toBits ≤ x) (hhi : x ≤ value hi.toBits) : Encloses (clamp a lo hi) x :=
  fun h => by
    obtain ⟨sa, hc⟩ := clamp_sound h
    exact hc x (ha sa) hlo hhi

theorem encloses_unit {a : Interval} {x : ℝ} (ha : Encloses a x) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Encloses (clamp a 0.0 1.0) x :=
  encloses_clamp _ _ ha (by rw [Conjunction.lit_zero.2]; exact h0)
    (by rw [Conjunction.lit_one.2]; exact h1)

theorem encloses_expI {a : Interval} {x : ℝ} (ha : Encloses a x) :
    Encloses (Conjunction.expI Exp.expTable a) (Real.exp x) := fun h => by
  obtain ⟨sa, hc⟩ := Conjunction.expI_sound h
  exact hc x (ha sa)

theorem erfc_antitone : Antitone RealErf.erfc := fun a b h => by
  unfold RealErf.erfc
  linarith [RealErf.erf_strictMono.monotone h]

theorem encloses_erfcI {a : Interval} {x : ℝ} (ha : Encloses a x) :
    Encloses (erfcT a) (RealErf.erfc x) := fun h => by
  unfold erfcT erfcI at h ⊢
  obtain ⟨sa, hc⟩ := decreasing_sound h (erfc_antitone.antitoneOn _)
    (fun hf => Erfc.ErfcTheorem.erfc_within_one _ hf)
    (fun hf => Erfc.ErfcTheorem.erfc_within_one _ hf)
  exact hc x (ha sa)

/-! ### The tail -/

/-- The divisor of step `j`, `2j + c`, as an `Int64`. -/
theorem divisor_toInt (j : ℕ) (c : UInt64) (hj : j < 2 ^ 32) (hc : c.toNat < 4) :
    ((UInt64.ofNat j) * 2 + c).toInt64.toInt = 2 * (j : ℤ) + c.toNat := by
  have hw : ((UInt64.ofNat j) * 2 + c).toNat = 2 * j + c.toNat := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat']
    have : (2 : UInt64).toNat = 2 := by decide
    rw [this]
    omega
  rw [Signed64Value.toInt_toInt64, hw, ite_eq_left (by omega)]
  push_cast
  ring

/-- After `j` steps of `terms` from the first term of shape `b/2`, the sum holds `A` plus the
first `j` terms and the term the next one, for `y = x/2`. -/
theorem terms_sound {px : Interval} {x : ℝ} (hpx : Encloses px x) (hx : 0 ≤ x) {b : ℕ}
    (hb : b < 2) {c m : UInt64} (hc : c.toNat = b + 2) (hm : m.toNat < 2 ^ 32) {acc t : Interval}
    {A : ℝ} (hacc : Encloses acc A) (hterm : Encloses t (Model.term ((b : ℝ) / 2) (x / 2))) :
    Encloses (terms px c m ⟨acc, t⟩).acc
      (A + ∑ i ∈ Finset.range m.toNat, Model.term ((b : ℝ) / 2 + i) (x / 2)) := by
  have hy : 0 ≤ x / 2 := by linarith
  refine (LeanExe.Dialect.loop_induction (n := m) (init := (⟨acc, t⟩ : Terms))
    (P := fun j s => Encloses s.acc
        (A + ∑ i ∈ Finset.range j, Model.term ((b : ℝ) / 2 + i) (x / 2)) ∧
      Encloses s.term (Model.term ((b : ℝ) / 2 + j) (x / 2)))
    ⟨by simpa using hacc, by simpa using hterm⟩ ?_).1
  intro j s hj ⟨ha, ht⟩
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_range_succ, ← add_assoc]
    exact encloses_add ha ht
  · have hd : Encloses (ofInt ((UInt64.ofNat j) * 2 + c).toInt64) (2 * (j : ℝ) + b + 2) :=
      encloses_ofInt' (divisor_toInt j c (by omega) (by omega)) (by omega)
        (by rw [hc]; push_cast; ring)
    have hstep := encloses_div (encloses_mul ht hpx) hd
    have ha0 : 0 ≤ (b : ℝ) / 2 + j := by positivity
    have heq : Model.term ((b : ℝ) / 2 + j) (x / 2) * x / (2 * (j : ℝ) + b + 2) =
        Model.term ((b : ℝ) / 2 + ((j + 1 : ℕ) : ℝ)) (x / 2) := by
      rw [show ((b : ℝ) / 2 + ((j + 1 : ℕ) : ℝ)) = ((b : ℝ) / 2 + j) + 1 by push_cast; ring,
        Model.term_succ ha0 hy]
      have : (0 : ℝ) < 2 * (j : ℝ) + b + 2 := by positivity
      field_simp
      ring
    rw [heq] at hstep
    have hk : ((b + 2 * (j + 1) : ℕ) : ℝ) / 2 = (b : ℝ) / 2 + ((j + 1 : ℕ) : ℝ) := by
      push_cast; ring
    refine encloses_unit hstep (Model.term_nonneg (by positivity) hy) ?_
    rw [← hk]
    exact Model.term_le_one (by omega) hy

theorem lit_zero_value : value (0.0 : Float).toBits = 0 := Conjunction.lit_zero.2

theorem nonneg_of_not_lt {x : Float} (hx : Finite x.toBits) (h : ¬ x < 0.0) :
    0 ≤ value x.toBits := by
  have := (lt_iff_value hx Conjunction.lit_zero.1).not.mp h
  rw [lit_zero_value] at this
  exact not_lt.mp this

theorem erf_sqrt_bounds (y : ℝ) : 0 ≤ RealErf.erfc (√y) ∧ RealErf.erfc (√y) ≤ 1 := by
  unfold RealErf.erfc
  have h1 := RealErf.erf_lt_one (√y)
  have h0 : RealErf.erf 0 ≤ RealErf.erf (√y) :=
    RealErf.erf_strictMono.monotone (Real.sqrt_nonneg y)
  rw [RealErf.erf_zero] at h0
  constructor <;> linarith

theorem toNat_mod_two (k : UInt64) : (k % 2 == 1) = true ↔ k.toNat % 2 = 1 := by
  rw [beq_iff_eq, ← UInt64.toNat_inj, UInt64.toNat_mod]
  simp

/-- The closed form of the tail at a point `x ≥ 0`. -/
theorem tailCore_sound {k : UInt64} {x : Float} (hk1 : 1 ≤ k.toNat) (hk2 : k.toNat ≤ 1000)
    (h0 : 0 ≤ value x.toBits) : Encloses (coreT k x) (Model.tail k.toNat (value x.toBits)) := by
  have hpx := encloses_point x
  set xr := value x.toBits
  have hy : 0 ≤ xr / 2 := by linarith
  have hyI : Encloses (clamp (mul (point x) (point 0.5)) 0.0 x) (xr / 2) := by
    have := encloses_mul hpx (encloses_lit Conjunction.Accuracy.lit_half)
    rw [show xr * (1 / 2) = xr / 2 by ring] at this
    exact encloses_clamp _ _ this (by rw [lit_zero_value]; exact hy) (by linarith)
  have heI : Encloses (clamp (Conjunction.expI Exp.expTable
      (neg (clamp (mul (point x) (point 0.5)) 0.0 x))) 0.0 1.0) (Real.exp (-(xr / 2))) :=
    encloses_unit (encloses_expI (encloses_neg hyI)) (Real.exp_pos _).le
      (Real.exp_le_one_iff.mpr (by linarith))
  have hm : (k / 2).toNat < 2 ^ 32 := by rw [UInt64.toNat_div]; simp; omega
  have hdiv : (k / 2).toNat = k.toNat / 2 := by rw [UInt64.toNat_div]; simp
  rw [Model.tail_closed hk1 h0]
  have hT : 0 ≤ Model.closedTail k.toNat (xr / 2) ∧ Model.closedTail k.toNat (xr / 2) ≤ 1 := by
    rw [← Model.tail_closed hk1 h0]
    exact ⟨Model.tail_nonneg _ _, Model.tail_le_one hk1 _⟩
  unfold coreT tailCore
  simp only
  by_cases hodd : (k % 2 == 1) = true
  · rw [ite_eq_left hodd]
    have hp := (toNat_mod_two k).mp hodd
    have hbase := encloses_unit (encloses_erfcI (encloses_sqrt hyI)) (erf_sqrt_bounds _).1
      (erf_sqrt_bounds _).2
    have hq : Encloses (clamp (div (clamp (mul (point x) (point 0.5)) 0.0 x) piI) 0.0 x)
        (xr / 2 / Real.pi) := by
      refine encloses_clamp _ _ (encloses_div hyI encloses_pi)
        (by rw [lit_zero_value]; positivity) ?_
      rw [div_le_iff₀ Real.pi_pos]
      nlinarith [Real.pi_gt_three]
    have hfirst : Encloses (clamp (mul (mul (point 2.0) (clamp (Conjunction.expI Exp.expTable
        (neg (clamp (mul (point x) (point 0.5)) 0.0 x))) 0.0 1.0)) (sqrt (clamp (div
        (clamp (mul (point x) (point 0.5)) 0.0 x) piI) 0.0 x))) 0.0 1.0)
        (Model.term (((1 : ℕ) : ℝ) / 2) (xr / 2)) := by
      have h := encloses_mul (encloses_mul (encloses_lit Conjunction.lit_two) heI)
        (encloses_sqrt hq)
      rw [← Model.term_half] at h
      refine encloses_unit (by simpa using h) (Model.term_nonneg (by norm_num) hy) ?_
      have := Model.term_le_one (k := 1) le_rfl hy
      simpa using this
    have hs := terms_sound hpx h0 (b := 1) (by norm_num) (c := 3) (by decide) hm hbase hfirst
    refine encloses_unit ?_ hT.1 hT.2
    unfold Model.closedTail
    rw [ite_eq_left hp, hp, ← hdiv]
    simpa [RealErf.erfc] using hs
  · rw [ite_eq_right hodd]
    have hp : k.toNat % 2 = 0 := by
      have := (toNat_mod_two k).not.mp hodd
      omega
    have hfirst : Encloses (clamp (Conjunction.expI Exp.expTable
        (neg (clamp (mul (point x) (point 0.5)) 0.0 x))) 0.0 1.0)
        (Model.term (((0 : ℕ) : ℝ) / 2) (xr / 2)) := by
      simpa [Model.term_zero_shape] using heI
    have hs := terms_sound hpx h0 (b := 0) (by norm_num) (c := 2) (by decide) hm
      (encloses_lit Conjunction.lit_zero) hfirst
    refine encloses_unit ?_ hT.1 hT.2
    unfold Model.closedTail
    rw [ite_eq_right (by omega), hp, ← hdiv]
    simpa using hs

theorem tail_one {k : ℕ} (hk : 1 ≤ k) {x : ℝ} (hx : x < 0) : Model.tail k x = 1 := by
  rw [Model.tail_eq_one_sub hk, Model.cdf_neg hk hx, sub_zero]

theorem tail_antitone {k : ℕ} (hk : 1 ≤ k) : Antitone (Model.tail k) := fun a b h => by
  have := Model.isProbability_of hk
  rw [Model.tail_eq_one_sub hk, Model.tail_eq_one_sub hk]
  have := ProbabilityTheory.monotone_cdf (Model.chiSquare k) h
  unfold Model.cdf
  linarith

theorem cut_bits : (1450.0 : Float).toBits = 0x4096A80000000000 := by decide +kernel

theorem lit_cut : Finite (1450.0 : Float).toBits ∧ value (1450.0 : Float).toBits = 1450 := by
  have hs : Wasm.IEEE64.scaledValue 0x4096A80000000000 = 1450 * 2 ^ 1074 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [cut_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [cut_bits, value, hs]; push_cast; norm_num

/-- An accepted result of `tail` belongs to `k` from 1 to 1,000 and a finite `x`, and it contains
the tail at the real value of `x`. -/
theorem tail_sound {k : UInt64} {x : Float} (h : (tail k x).status = 0) :
    1 ≤ k.toNat ∧ k.toNat ≤ 1000 ∧ Finite x.toBits ∧
      Contains (tail k x) (Model.tail k.toNat (value x.toBits)) := by
  unfold tail tailWith at h ⊢
  by_cases g1 : finite x = true
  · rw [ite_eq_left g1] at h ⊢
    have hx := (finite_iff x).mp g1
    by_cases g2 : 1 ≤ k ∧ k ≤ 1000
    · rw [ite_eq_left g2] at h ⊢
      have hk1 : 1 ≤ k.toNat := UInt64.le_iff_toNat_le.mp g2.1
      have hk2 : k.toNat ≤ 1000 := UInt64.le_iff_toNat_le.mp g2.2
      refine ⟨hk1, hk2, hx, ?_⟩
      by_cases g3 : x < 0.0
      · rw [ite_eq_left g3] at h ⊢
        have hneg : value x.toBits < 0 := by
          have := (lt_iff_value hx Conjunction.lit_zero.1).mp g3
          rwa [lit_zero_value] at this
        rw [tail_one hk1 hneg]
        exact encloses_lit Conjunction.lit_one h
      · rw [ite_eq_right g3] at h ⊢
        have h0 := nonneg_of_not_lt hx g3
        by_cases g4 : x ≤ 1450.0
        · rw [ite_eq_left g4] at h ⊢
          exact tailCore_sound hk1 hk2 h0 h
        · rw [ite_eq_right g4] at h ⊢
          simp only at h ⊢
          by_cases g5 : ((coreT k 1450.0).status == 0) = true
          · rw [ite_eq_left g5] at h ⊢
            have hc := tailCore_sound hk1 hk2 (by rw [lit_cut.2]; norm_num)
              (beq_iff_eq.mp g5)
            rw [lit_cut.2] at hc
            have hgt : 1450 < value x.toBits := by
              have := (le_iff_value hx lit_cut.1).not.mp g4
              rw [lit_cut.2] at this
              exact not_le.mp this
            obtain ⟨-, -, -, hall⟩ := make_sound h
            refine hall _ (by rw [lit_zero_value]; exact Model.tail_nonneg _ _) ?_
            exact (tail_antitone hk1 hgt.le).trans hc.2.2.2.2
          · rw [ite_eq_right g5] at h
            exact absurd h (by decide)
    · rw [ite_eq_right g2] at h
      exact absurd h (by decide)
  · rw [ite_eq_right g1] at h
    exact absurd h (by decide)

/-- An accepted result of `cdf` belongs to `k` from 1 to 1,000 and a finite `x`, and it contains
the distribution function at the real value of `x`. -/
theorem cdf_sound {k : UInt64} {x : Float} (h : (cdf k x).status = 0) :
    1 ≤ k.toNat ∧ k.toNat ≤ 1000 ∧ Finite x.toBits ∧
      Contains (cdf k x) (Model.cdf k.toNat (value x.toBits)) := by
  unfold cdf cdfWith at h ⊢
  obtain ⟨s1, -⟩ := clamp_sound h
  obtain ⟨-, s2, -⟩ := sub_sound s1
  obtain ⟨hk1, hk2, hx, ht⟩ := tail_sound (k := k) (x := x) s2
  refine ⟨hk1, hk2, hx, ?_⟩
  have he : Encloses (sub (point 1.0) (tail k x)) (1 - Model.tail k.toNat (value x.toBits)) :=
    encloses_sub (encloses_lit Conjunction.lit_one) fun _ => ht
  rw [Model.tail_eq_one_sub hk1, sub_sub_cancel] at he
  have hc0 : 0 ≤ Model.cdf k.toNat (value x.toBits) := ProbabilityTheory.cdf_nonneg _ _
  have hc1 : Model.cdf k.toNat (value x.toBits) ≤ 1 := ProbabilityTheory.cdf_le_one _ _
  exact encloses_unit he hc0 hc1 h

/-! ### The quantile -/

theorem cdfAt_sound {k : UInt64} {x : Float} (h : (cdfAtT k x).status = 0) :
    1 ≤ k.toNat ∧ Finite x.toBits ∧ 0 ≤ value x.toBits ∧
      Contains (cdfAtT k x) (Model.cdf k.toNat (value x.toBits)) := by
  unfold cdfAtT cdfAt at h ⊢
  by_cases g : (0.0 : Float) ≤ x
  · rw [ite_eq_left g] at h ⊢
    obtain ⟨hk1, -, hx, hc⟩ := cdf_sound (k := k) (x := x) h
    have h0 : 0 ≤ value x.toBits := by
      have := (le_iff_value Conjunction.lit_zero.1 hx).mp g
      rwa [lit_zero_value] at this
    exact ⟨hk1, hx, h0, hc⟩
  · rw [ite_eq_right g] at h
    exact absurd h (by decide)

/-- A finite point at or above zero whose distribution function lies below `q`. -/
def Below (k : ℕ) (q : ℝ) (x : Float) : Prop :=
  Finite x.toBits ∧ 0 ≤ value x.toBits ∧ Model.cdf k (value x.toBits) < q

/-- A finite point at or above zero whose distribution function is at least `q`. -/
def Above (k : ℕ) (q : ℝ) (x : Float) : Prop :=
  Finite x.toBits ∧ 0 ≤ value x.toBits ∧ q ≤ Model.cdf k (value x.toBits)

theorem raise_below {k : UInt64} {p : Float} (hp : Finite p.toBits) (h : UInt64) {b : Ends}
    (hb : Below k.toNat (value p.toBits) b.lo) :
    Below k.toNat (value p.toBits) (raise Exp.expTable Erfc.fastTable Erfc.accTable
      Erfc.expTable Erfc.asymTable Erfc.asymAccTable Erfc.expAccTable Erfc.excTable k p h b).lo := by
  unfold raise
  refine LeanExe.Dialect.loop_induction (P := fun _ (e : Ends) => Below k.toNat (value p.toBits) e.lo)
    hb fun _ e _ he => ?_
  simp only
  by_cases g : ((cdfAtT k (split e)).status == 0 && (cdfAtT k (split e)).hi < p) = true
  · rw [ite_eq_left g]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g
    obtain ⟨-, fx, h0, hc⟩ := cdfAt_sound g.1
    exact ⟨fx, h0, lt_of_le_of_lt hc.2.2.2.2 ((lt_iff_value hc.2.2.1 hp).mp g.2)⟩
  · rw [ite_eq_right g]
    exact he

theorem lower_above {k : UInt64} {p : Float} (hp : Finite p.toBits) (h : UInt64) {b : Ends}
    (hb : Above k.toNat (value p.toBits) b.hi) :
    Above k.toNat (value p.toBits) (lower Exp.expTable Erfc.fastTable Erfc.accTable
      Erfc.expTable Erfc.asymTable Erfc.asymAccTable Erfc.expAccTable Erfc.excTable k p h b).hi := by
  unfold lower
  refine LeanExe.Dialect.loop_induction (P := fun _ (e : Ends) => Above k.toNat (value p.toBits) e.hi)
    hb fun _ e _ he => ?_
  simp only
  by_cases g : ((cdfAtT k (split e)).status == 0 && p ≤ (cdfAtT k (split e)).lo) = true
  · rw [ite_eq_left g]
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g
    obtain ⟨-, fx, h0, hc⟩ := cdfAt_sound g.1
    exact ⟨fx, h0, ((le_iff_value hp hc.2.1).mp g.2).trans hc.2.2.2.1⟩
  · rw [ite_eq_right g]
    exact he

/-- An accepted result of `quantile` holds the quantile at `p` of the chi-square distribution
with `k` degrees of freedom, for the real value of `p`. -/
theorem quantile_sound {k : UInt64} {p : Float} {h : UInt64} (hs : (quantile k p h).status = 0) :
    0 < value p.toBits ∧ value p.toBits < 1 ∧ 1 ≤ k.toNat ∧ k.toNat ≤ 1000 ∧
      Finite (quantile k p h).lo.toBits ∧ Finite (quantile k p h).hi.toBits ∧
      Model.QuantileIn k.toNat (value p.toBits) (value (quantile k p h).lo.toBits)
        (value (quantile k p h).hi.toBits) := by
  unfold quantile quantileWith at hs ⊢
  by_cases g1 : finite p = true
  · rw [ite_eq_left g1] at hs ⊢
    have fp := (finite_iff p).mp g1
    by_cases g2 : (0.0 : Float) < p ∧ p < 1.0 ∧ 1 ≤ k ∧ k ≤ 1000 ∧ h ≤ 64
    · rw [ite_eq_left g2] at hs ⊢
      have hq : 0 < value p.toBits := by
        have := (lt_iff_value Conjunction.lit_zero.1 fp).mp g2.1
        rwa [lit_zero_value] at this
      have hq1 : value p.toBits < 1 := by
        have := (lt_iff_value fp Conjunction.lit_one.1).mp g2.2.1
        rwa [Conjunction.lit_one.2] at this
      have hk1 : 1 ≤ k.toNat := UInt64.le_iff_toNat_le.mp g2.2.2.1
      have hk2 : k.toNat ≤ 1000 := UInt64.le_iff_toNat_le.mp g2.2.2.2.1
      simp only at hs ⊢
      by_cases g3 : ((cdfAtT k (bound k)).status == 0 && p ≤ (cdfAtT k (bound k)).lo) = true
      · rw [ite_eq_left g3] at hs ⊢
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at g3
        obtain ⟨-, fb, hb0, hcb⟩ := cdfAt_sound g3.1
        have hlo : Below k.toNat (value p.toBits) (0.0 : Float) :=
          ⟨Conjunction.lit_zero.1, by rw [lit_zero_value],
            by rw [lit_zero_value, Model.cdf_zero hk1]; exact hq⟩
        have hhi : Above k.toNat (value p.toBits) (bound k) :=
          ⟨fb, hb0, ((le_iff_value fp hcb.2.1).mp g3.2).trans hcb.2.2.2.1⟩
        have ha := raise_below (b := ⟨0.0, bound k⟩) fp h hlo
        have hc := lower_above (b := ⟨0.0, bound k⟩) fp h hhi
        exact ⟨hq, hq1, hk1, hk2, ha.1, hc.1,
          Model.quantileIn_of hk1 hq ha.2.1 hc.2.1 ha.2.2 hc.2.2⟩
      · rw [ite_eq_right g3] at hs
        exact absurd hs (by decide)
    · rw [ite_eq_right g2] at hs
      exact absurd hs (by decide)
  · rw [ite_eq_right g1] at hs
    exact absurd hs (by decide)

#print axioms tail_sound
#print axioms cdf_sound
#print axioms quantile_sound

end Demos.Gate
