import Demos.Orbit.LambertBox
import Demos.Orbit.GibbsSound
import Library.Numerics.Float64.Asin.AcosTheorem
import Library.Numerics.Float64.Log.LogTheorem
import LeanExe.Dialect.Lemmas

/-!
Soundness of Lambert's interval program.  `tofI_encloses` states that `tofI` encloses Izzo's time
of flight at a binary64 point, `raise_spec` and `lower_spec` state the invariants of the two
bisections, and `lambertBox_sound` (L4) states that a result with status 0 contains the root of
Izzo's equation and Izzo's velocities at it, for every input in the boxes.
-/

namespace Demos.Orbit

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64 V3 Real
open LeanExe.ProofKit
open CodeLib.IEEE64 (value Finite)

/-! ### Real facts -/

theorem sqrt_max_zero (u : ℝ) : √(max u 0) = √u := by
  rcases le_total 0 u with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, sqrt_zero, sqrt_eq_zero_of_nonpos h]

/-- The argument of `arccos` in `ψ` lies in `[-1, 1]`. -/
theorem psi_arg_mem {lam x : ℝ} (hl0 : -1 < lam) (hl1 : lam < 1) (hx0 : -1 < x) (hx1 : x < 1) :
    -1 ≤ x * Lambert.yOf lam x + lam * (1 - x ^ 2) ∧
      x * Lambert.yOf lam x + lam * (1 - x ^ 2) ≤ 1 := by
  have hs2 : √(1 - x ^ 2) ^ 2 = 1 - x ^ 2 := sq_sqrt (by nlinarith)
  have hs0 : 0 ≤ √(1 - x ^ 2) := sqrt_nonneg _
  have hs1 : √(1 - x ^ 2) ≤ 1 := by nlinarith
  have hls1 : -1 ≤ lam * √(1 - x ^ 2) := by nlinarith
  have hls2 : lam * √(1 - x ^ 2) ≤ 1 := by nlinarith
  have hc : cos (arccos x - arcsin (lam * √(1 - x ^ 2))) =
      x * Lambert.yOf lam x + lam * (1 - x ^ 2) := by
    rw [cos_sub, cos_arccos hx0.le hx1.le, sin_arccos, sin_arcsin hls1 hls2, cos_arcsin,
      Lambert.yOf, mul_pow, hs2]
    linear_combination lam * hs2
  rw [← hc]
  exact ⟨neg_one_le_cos _, cos_le_one _⟩

/-! ### Enclosures of `arccos`, `log`, and `arcosh` -/

theorem oneI_encloses : Encloses oneI (1 : ℝ) :=
  encloses_ofInt' (n := 1) (m := 1) (by decide +kernel) (by decide +kernel) (by norm_num)

theorem zeroI_encloses : Encloses (ofInt 0) (0 : ℝ) :=
  encloses_ofInt' (n := 0) (m := 0) (by decide +kernel) (by decide +kernel) (by norm_num)

theorem clamp_lo {a : Interval} {lo hi : Float} (h : (clamp a lo hi).status = 0) :
    (clamp a lo hi).lo = fmax a.lo lo ∧ (clamp a lo hi).hi = fmin a.hi hi := by
  unfold clamp at h ⊢
  split_ifs at h ⊢ with hc
  · exact ⟨rfl, rfl⟩
  · exact absurd h (by decide)

theorem acosI_encloses {a : Interval} {z : ℝ} (ha : Encloses a z) (h0 : -1 ≤ z) (h1 : z ≤ 1) :
    Encloses (acosI a) (arccos z) := by
  intro hs
  unfold acosI at hs ⊢
  have hb : (clamp a (-1.0) 1.0).status = 0 := by
    unfold decreasing at hs; exact beq_iff_eq.mp (join_accepted hs).1
  obtain ⟨ha0, hcl⟩ := clamp_sound hb
  obtain ⟨f1, v1⟩ := one_value
  have fm1 : Finite (-1.0 : Float).toBits := (neg_value f1).1
  have vm1 : value (-1.0 : Float).toBits = -1 := unit_bounds.1
  have cz := ha ha0
  have cb := hcl z cz (by rw [vm1]; exact h0) (by rw [v1]; exact h1)
  obtain ⟨elo, ehi⟩ := clamp_lo hb
  have blo : -1 ≤ value (clamp a (-1.0) 1.0).lo.toBits := by
    rw [elo, (fmax_value cz.2.1 fm1).2, vm1]; exact le_max_right _ _
  have bhi : value (clamp a (-1.0) 1.0).hi.toBits ≤ 1 := by
    rw [ehi, (fmin_value cz.2.2.1 f1).2, v1]; exact min_le_right _ _
  have zlo := cb.2.2.2.1
  have zhi := cb.2.2.2.2
  refine (decreasing_sound hs (antitone_arccos.antitoneOn _) ?_ ?_).2 z cb
  · intro hf
    exact Asin.AcosTheorem.acos_within_one _ hf (abs_le.mpr ⟨blo, by linarith⟩)
  · intro hf
    exact Asin.AcosTheorem.acos_within_one _ hf (abs_le.mpr ⟨by linarith, bhi⟩)

theorem logI_encloses {a : Interval} {z : ℝ} (ha : Encloses a z) :
    Encloses (logI Log.logTable Log.logTable2 a) (Real.log z) := by
  intro hs
  unfold logI at hs ⊢
  split_ifs at hs ⊢ with hp
  · have ha0 : a.status = 0 := by
      unfold increasing at hs; exact beq_iff_eq.mp (join_accepted hs).1
    have cz := ha ha0
    obtain ⟨z0, zv⟩ := zero_value
    have lo0 : 0 < value a.lo.toBits := by rw [← zv]; exact (lt_iff_value z0 cz.2.1).mp hp
    have hmono : MonotoneOn Real.log (Set.Icc (value a.lo.toBits) (value a.hi.toBits)) :=
      Real.strictMonoOn_log.monotoneOn.mono fun u hu => lt_of_lt_of_le lo0 hu.1
    refine (increasing_sound hs hmono ?_ ?_).2 z cz
    · intro hf; exact Log.LogTheorem.log_within_one _ hf lo0
    · intro hf
      exact Log.LogTheorem.log_within_one _ hf (lo0.trans_le (cz.2.2.2.1.trans cz.2.2.2.2))
  · exact absurd hs (by decide)

theorem arcoshI_encloses {a : Interval} {z : ℝ} (ha : Encloses a z) :
    Encloses (arcoshI Log.logTable Log.logTable2 a) (arcosh z) := by
  have h := logI_encloses (encloses_add ha (encloses_sqrt (encloses_imax
    (encloses_sub (encloses_sq ha) oneI_encloses) zeroI_encloses)))
  rw [sqrt_max_zero, show z * z - 1 = z ^ 2 - 1 by ring] at h
  unfold arcoshI arcosh
  exact h

/-! ### The time of flight -/

theorem point_encloses (m : Float) : Encloses (point m) (value m.toBits) :=
  fun h => (point_sound h).2

/-- `tofI` encloses Izzo's time of flight at a finite binary64 point above -1. -/
theorem tofI_encloses {l : Interval} {lam : ℝ} {m : Float} (hl : Encloses l lam)
    (hl0 : -1 < lam) (hl1 : lam < 1) (hm : Finite m.toBits) (hm1 : -1 < value m.toBits) :
    Encloses (tofI Log.logTable Log.logTable2 l m) (Lambert.tof lam (value m.toBits)) := by
  have hx := point_encloses m
  have one := oneI_encloses
  obtain ⟨f1, v1⟩ := one_value
  set x := value m.toBits with hxdef
  unfold tofI
  by_cases c1 : m < 1.0
  · have hlt : x < 1 := by rw [← v1]; exact (lt_iff_value hm f1).mp c1
    simp only [c1, ↓reduceIte]
    have hw := encloses_mul (encloses_sub one hx) (encloses_add one hx)
    have hy := encloses_sqrt (encloses_imax (encloses_sub one (encloses_mul (encloses_sq hl) hw))
      zeroI_encloses)
    rw [sqrt_max_zero] at hy
    have hg := encloses_add (encloses_mul hx hy) (encloses_mul hl hw)
    have ew : (1 - x) * (1 + x) = 1 - x ^ 2 := by ring
    have ey : √(1 - lam * lam * ((1 - x) * (1 + x))) = Lambert.yOf lam x := by
      rw [Lambert.yOf]; congr 1; ring
    rw [ey, ew] at hg
    have bounds := psi_arg_mem hl0 hl1 hm1 hlt
    have hpsi := acosI_encloses hg bounds.1 bounds.2
    have hr := encloses_div (encloses_add (encloses_sub (encloses_div hpsi (encloses_sqrt hw)) hx)
      (encloses_mul hl hy)) hw
    rw [ey, ew] at hr
    simpa only [Lambert.tof, hlt, ↓reduceIte] using hr
  · have hge : 1 ≤ x := by
      rw [← v1]; exact not_lt.mp fun h => c1 ((lt_iff_value hm f1).mpr h)
    by_cases c2 : 1.0 < m
    · have hgt : 1 < x := by rw [← v1]; exact (lt_iff_value f1 hm).mp c2
      simp only [c1, c2, ↓reduceIte]
      have hv := encloses_mul (encloses_sub hx one) (encloses_add hx one)
      have hy := encloses_sqrt (encloses_add one (encloses_mul (encloses_sq hl) hv))
      have hg := encloses_sub (encloses_mul hx hy) (encloses_mul hl hv)
      have ev : (x - 1) * (x + 1) = x ^ 2 - 1 := by ring
      have ey : √(1 + lam * lam * ((x - 1) * (x + 1))) = Lambert.yOf lam x := by
        rw [Lambert.yOf]; congr 1; ring
      rw [ey, ev] at hg
      have hpsi := arcoshI_encloses hg
      have hr := encloses_div (encloses_add (encloses_sub (encloses_div hpsi (encloses_sqrt hv)) hx)
        (encloses_mul hl hy)) (encloses_neg hv)
      rw [ey, ev, show -(x ^ 2 - 1) = 1 - x ^ 2 by ring] at hr
      simpa only [Lambert.tof, not_lt.mpr hge, hgt.ne', ↓reduceIte] using hr
    · have hle : x ≤ 1 := by
        rw [← v1]; exact not_lt.mp fun h => c2 ((lt_iff_value f1 hm).mpr h)
      have heq : x = 1 := le_antisymm hle hge
      simp only [c1, c2, ↓reduceIte]
      have two3 : Encloses (ratio 2 3) (2 / 3 : ℝ) :=
        encloses_ratio' (m := 2) (k := 3) (by decide +kernel) (by decide +kernel)
          (by decide +kernel) (by decide +kernel) (by norm_num)
      have hr := encloses_mul two3 (encloses_sub one (encloses_mul (encloses_sq hl) hl))
      rw [show lam * lam * lam = lam ^ 3 by ring] at hr
      simpa only [Lambert.tof, heq, lt_irrefl, ↓reduceIte] using hr

/-- What `above` shows. -/
theorem above_sound {l tt : Interval} {lam T : ℝ} {m : Float}
    (h : above Log.logTable Log.logTable2 l tt m = true) (hl : Contains l lam)
    (ht : Contains tt T) (hl0 : -1 < lam) (hl1 : lam < 1) (hm : Finite m.toBits)
    (hm1 : -1 < value m.toBits) : T < Lambert.tof lam (value m.toBits) := by
  simp only [above, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have c := tofI_encloses (fun _ => hl) hl0 hl1 hm hm1 h.1
  have := (lt_iff_value ht.2.2.1 c.2.1).mp h.2
  linarith [ht.2.2.2.2, c.2.2.2.1]

/-- What `below` shows. -/
theorem below_sound {l tt : Interval} {lam T : ℝ} {m : Float}
    (h : below Log.logTable Log.logTable2 l tt m = true) (hl : Contains l lam)
    (ht : Contains tt T) (hl0 : -1 < lam) (hl1 : lam < 1) (hm : Finite m.toBits)
    (hm1 : -1 < value m.toBits) : Lambert.tof lam (value m.toBits) < T := by
  simp only [below, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  have c := tofI_encloses (fun _ => hl) hl0 hl1 hm hm1 h.1
  have := (lt_iff_value c.2.2.1 ht.2.1).mp h.2
  linarith [ht.2.2.2.1, c.2.2.2.2]

/-! ### The bisections -/

/-- The invariant of the bisection that raises `a`. -/
def RaiseInv (lam T : ℝ) (s : Search) : Prop :=
  Finite s.a.toBits ∧ -1 < value s.a.toBits ∧ T < Lambert.tof lam (value s.a.toBits)

/-- The invariant of the bisection that lowers `b`. -/
def LowerInv (lam T : ℝ) (s : Search) : Prop :=
  Finite s.a.toBits ∧ -1 < value s.a.toBits ∧ Finite s.b.toBits ∧ -1 < value s.b.toBits ∧
    Lambert.tof lam (value s.b.toBits) < T

theorem raiseStep_inv {l tt : Interval} {lam T : ℝ} (hl : Contains l lam) (ht : Contains tt T)
    (hl0 : -1 < lam) (hl1 : lam < 1) {s : Search} (h : RaiseInv lam T s) :
    RaiseInv lam T (raiseStep Log.logTable Log.logTable2 l tt s) := by
  unfold raiseStep
  dsimp only
  split_ifs with hd hf hm ha
  · exact h
  · rw [finite_iff] at hf
    have hlt : value s.a.toBits < value (midpoint s).toBits := (lt_iff_value h.1 hf).mp hm.1
    have hm1 : -1 < value (midpoint s).toBits := by linarith [h.2.1]
    exact ⟨hf, hm1, above_sound ha hl ht hl0 hl1 hf hm1⟩
  · exact h
  · exact h
  · exact h

theorem lowerStep_inv {l tt : Interval} {lam T : ℝ} (hl : Contains l lam) (ht : Contains tt T)
    (hl0 : -1 < lam) (hl1 : lam < 1) {s : Search} (h : LowerInv lam T s) :
    LowerInv lam T (lowerStep Log.logTable Log.logTable2 l tt s) := by
  unfold lowerStep
  dsimp only
  split_ifs with hd hf hm hb
  · exact h
  · rw [finite_iff] at hf
    have hlt : value s.a.toBits < value (midpoint s).toBits := (lt_iff_value h.1 hf).mp hm.1
    have hm1 : -1 < value (midpoint s).toBits := by linarith [h.2.1]
    exact ⟨h.1, h.2.1, hf, hm1, below_sound hb hl ht hl0 hl1 hf hm1⟩
  · rw [finite_iff] at hf
    have hlt : value s.a.toBits < value (midpoint s).toBits := (lt_iff_value h.1 hf).mp hm.1
    exact ⟨hf, by linarith [h.2.1], h.2.2⟩
  · exact h
  · exact h

/-- The starting bracket keeps the invariants of both searches. -/
theorem bracket_spec {l tt : Interval} {lam T : ℝ} (hl : Contains l lam) (ht : Contains tt T)
    (hl0 : -1 < lam) (hl1 : lam < 1) {a0 b0 : Float} (ha : RaiseInv lam T ⟨a0, b0, false⟩)
    (hb : LowerInv lam T ⟨a0, b0, false⟩) :
    RaiseInv lam T ⟨(bracket Log.logTable Log.logTable2 l tt a0 b0).a,
        (bracket Log.logTable Log.logTable2 l tt a0 b0).b, false⟩ ∧
      LowerInv lam T ⟨(bracket Log.logTable Log.logTable2 l tt a0 b0).a,
        (bracket Log.logTable Log.logTable2 l tt a0 b0).b, false⟩ := by
  obtain ⟨f1, v1⟩ := one_value
  have g1 : -1 < value (1.0 : Float).toBits := by rw [v1]; norm_num
  unfold bracket
  split_ifs with h1 h2
  · exact ⟨⟨f1, g1, above_sound h1 hl ht hl0 hl1 f1 g1⟩, ⟨f1, g1, hb.2.2⟩⟩
  · exact ⟨ha, ⟨ha.1, ha.2.1, f1, g1, below_sound h2 hl ht hl0 hl1 f1 g1⟩⟩
  · exact ⟨ha, hb⟩

theorem raise_spec {l tt : Interval} {lam T : ℝ} (hl : Contains l lam) (ht : Contains tt T)
    (hl0 : -1 < lam) (hl1 : lam < 1) {a b : Float} (h : RaiseInv lam T ⟨a, b, false⟩) :
    RaiseInv lam T (raise Log.logTable Log.logTable2 l tt a b) := by
  unfold raise
  exact LeanExe.Dialect.loop_induction (fun _ s => RaiseInv lam T s) h
    (fun _ _ _ hs => raiseStep_inv hl ht hl0 hl1 hs)

theorem lower_spec {l tt : Interval} {lam T : ℝ} (hl : Contains l lam) (ht : Contains tt T)
    (hl0 : -1 < lam) (hl1 : lam < 1) {a b : Float} (h : LowerInv lam T ⟨a, b, false⟩) :
    LowerInv lam T (lower Log.logTable Log.logTable2 l tt a b) := by
  unfold lower
  exact LeanExe.Dialect.loop_induction (fun _ s => LowerInv lam T s) h
    (fun _ _ _ hs => lowerStep_inv hl ht hl0 hl1 hs)

/-! ### The real model of the program -/

/-- The sign of the direction of motion: 1 when `(r1 × r2) · k > 0` and -1 otherwise. -/
noncomputable def motionSign (r1 r2 k : V3) : ℝ := if 0 < dot (cross r1 r2) k then 1 else -1

/-- Izzo's `λ` and `T` for the positions, the time of flight, `μ`, and the axis `k`. -/
noncomputable def izzoParams (r1 r2 : V3) (t μ : ℝ) (k : V3) : ℝ × ℝ :=
  geometry r1.x r1.y r1.z r2.x r2.y r2.z t μ (motionSign r1 r2 k)

/-- The root of Izzo's equation and Izzo's velocities at it. -/
noncomputable def solution (r1 r2 : V3) (t μ : ℝ) (k : V3) :
    ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ :=
  let x := Lambert.root (izzoParams r1 r2 t μ k).1 (izzoParams r1 r2 t μ k).2
  (x, velocities r1.x r1.y r1.z r2.x r2.y r2.z μ (motionSign r1 r2 k) x)

/-- The intervals of a result contain the root and the velocities. -/
def Inside (tr : Transfer) (sol : ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) : Prop :=
  Contains tr.x sol.1 ∧ Contains tr.v1x sol.2.1 ∧ Contains tr.v1y sol.2.2.1 ∧
    Contains tr.v1z sol.2.2.2.1 ∧ Contains tr.v2x sol.2.2.2.2.1 ∧
    Contains tr.v2y sol.2.2.2.2.2.1 ∧ Contains tr.v2z sol.2.2.2.2.2.2

theorem direction_eq (r1 r2 k : V3) :
    direction r1.x r1.y r1.z r2.x r2.y r2.z k.x k.y k.z = dot (cross r1 r2) k := by
  simp only [direction, dot, cross_x, cross_y, cross_z]

theorem chord_pos {r1 r2 k : V3} (hD : dot (cross r1 r2) k ≠ 0) :
    0 < lengthOf (r2.x - r1.x) (r2.y - r1.y) (r2.z - r1.z) := by
  unfold lengthOf sqr
  apply sqrt_pos.mpr
  by_contra hc
  push Not at hc
  have hx : r2.x - r1.x = 0 := by
    nlinarith [mul_self_nonneg (r2.x - r1.x), mul_self_nonneg (r2.y - r1.y),
      mul_self_nonneg (r2.z - r1.z)]
  have hy : r2.y - r1.y = 0 := by
    nlinarith [mul_self_nonneg (r2.x - r1.x), mul_self_nonneg (r2.y - r1.y),
      mul_self_nonneg (r2.z - r1.z)]
  have hz : r2.z - r1.z = 0 := by
    nlinarith [mul_self_nonneg (r2.x - r1.x), mul_self_nonneg (r2.y - r1.y),
      mul_self_nonneg (r2.z - r1.z)]
  apply hD
  have : r2 = r1 := by ext <;> linarith
  rw [this]
  simp only [dot, cross_x, cross_y, cross_z]
  ring

theorem lengthOf_nonneg (a b c : ℝ) : 0 ≤ lengthOf a b c := sqrt_nonneg _

/-- `λ` lies strictly between -1 and 1 when the chord is positive. -/
theorem lam_bounds {n1 n2 c sg : ℝ} (hn1 : 0 ≤ n1) (hn2 : 0 ≤ n2) (hc : 0 < c)
    (hsg : sg = 1 ∨ sg = -1) :
    -1 < sg * √(max (1 - c / ((n1 + n2 + c) / 2)) 0) ∧
      sg * √(max (1 - c / ((n1 + n2 + c) / 2)) 0) < 1 := by
  have hs : 0 < (n1 + n2 + c) / 2 := by linarith
  have hq : 0 < c / ((n1 + n2 + c) / 2) := div_pos hc hs
  have hm : max (1 - c / ((n1 + n2 + c) / 2)) 0 < 1 := max_lt (by linarith) one_pos
  have hr : √(max (1 - c / ((n1 + n2 + c) / 2)) 0) < 1 :=
    (sqrt_lt' one_pos).mpr (by rw [one_pow]; exact hm)
  have hr0 := sqrt_nonneg (max (1 - c / ((n1 + n2 + c) / 2)) 0)
  rcases hsg with h | h <;> rw [h] <;> constructor <;> linarith

theorem geometryI_tables (x1 y1 z1 x2 y2 z2 t mu sg : Interval) :
    geometryI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 t mu sg =
      geometryI Trig.invPi Trig.halfPi noTable noTable x1 y1 z1 x2 y2 z2 t mu sg := rfl

theorem directionI_tables (x1 y1 z1 x2 y2 z2 kx ky kz : Interval) :
    directionI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 kx ky kz =
      directionI Trig.invPi Trig.halfPi noTable noTable x1 y1 z1 x2 y2 z2 kx ky kz := rfl

theorem velocitiesI_tables (x1 y1 z1 x2 y2 z2 mu sg xx : Interval) :
    velocitiesI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 mu sg xx =
      velocitiesI Trig.invPi Trig.halfPi noTable noTable x1 y1 z1 x2 y2 z2 mu sg xx := rfl

theorem neg_oneI_encloses : Encloses (neg oneI) (-1 : ℝ) := encloses_neg oneI_encloses

/-- `solve` with `λ` in `l` and `T` in `tt` returns intervals that contain the root and the
velocities. -/
theorem solve_sound {x1 y1 z1 x2 y2 z2 mu sg l tt : Interval} {r1 r2 : V3} {μ sgr lam T : ℝ}
    (hs : (solve Log.logTable Log.logTable2 x1 y1 z1 x2 y2 z2 mu sg l tt).status = 0)
    (b1 : InBox x1 y1 z1 r1) (b2 : InBox x2 y2 z2 r2) (hμ : Contains mu μ)
    (hsg : Encloses sg sgr) (hl : Contains l lam) (ht : Contains tt T)
    (hl0 : -1 < lam) (hl1 : lam < 1) (hT : 0 < T) :
    Inside (solve Log.logTable Log.logTable2 x1 y1 z1 x2 y2 z2 mu sg l tt)
      (Lambert.root lam T,
        velocities r1.x r1.y r1.z r2.x r2.y r2.z μ sgr (Lambert.root lam T)) := by
  obtain ⟨f1, v1⟩ := one_value
  have fm1 : Finite (-1.0 : Float).toBits := (neg_value f1).1
  have vm1 : value (-1.0 : Float).toBits = -1 := unit_bounds.1
  unfold solve at hs ⊢
  dsimp only at hs ⊢
  split_ifs at hs ⊢ with hfin hgt hab hdone hst
  · simp only [Bool.and_eq_true, finite_iff] at hfin
    simp only [Bool.and_eq_true] at hab hdone
    simp only [Bool.and_eq_true, beq_iff_eq] at hst
    obtain ⟨fa, fb⟩ := hfin
    have ga : -1 < value startLow.toBits := by rw [← vm1]; exact (lt_iff_value fm1 fa).mp hgt.1
    have gb : -1 < value (1.0 + 4.0 / tt.lo).toBits := by
      rw [← vm1]; exact (lt_iff_value fm1 fb).mp hgt.2
    have ia : RaiseInv lam T ⟨startLow, 1.0 + 4.0 / tt.lo, false⟩ :=
      ⟨fa, ga, above_sound hab.1 hl ht hl0 hl1 fa ga⟩
    have ib : LowerInv lam T ⟨startLow, 1.0 + 4.0 / tt.lo, false⟩ :=
      ⟨fa, ga, fb, gb, below_sound hab.2 hl ht hl0 hl1 fb gb⟩
    obtain ⟨ja, jb⟩ := bracket_spec hl ht hl0 hl1 ia ib
    have ra := raise_spec hl ht hl0 hl1 ja
    have lb := lower_spec hl ht hl0 hl1 jb
    obtain ⟨h1, h2⟩ := Lambert.root_between hl0 hl1 hT ra.2.1 lb.2.2.2.1 ra.2.2 lb.2.2.2.2
    have hxx := (make_sound hst.1.1.1.1.1.1).2.2.2 _ h1.le h2.le
    have hv := velocities.encloses (powLog := noTable) (powExp := noTable)
      (b1.encloses.1) (b1.encloses.2.1) (b1.encloses.2.2) (b2.encloses.1) (b2.encloses.2.1)
      (b2.encloses.2.2) (fun _ => hμ) hsg (fun _ => hxx)
    rw [← velocitiesI_tables] at hv
    exact ⟨hxx, hv.1 hst.1.1.1.1.1.2, hv.2.1 hst.1.1.1.1.2, hv.2.2.1 hst.1.1.1.2,
      hv.2.2.2.1 hst.1.1.2, hv.2.2.2.2.1 hst.1.2, hv.2.2.2.2.2 hst.2⟩
  all_goals simp [noTransfer] at hs

theorem direction_eq' (r1 r2 : V3) (a b c : ℝ) :
    direction r1.x r1.y r1.z r2.x r2.y r2.z a b c = dot (cross r1 r2) ⟨a, b, c⟩ := by
  simp only [direction, dot, cross_x, cross_y, cross_z]

theorem izzoParams_fst (r1 r2 : V3) (t μ : ℝ) (k : V3) :
    (izzoParams r1 r2 t μ k).1 = motionSign r1 r2 k *
      √(max (1 - lengthOf (r2.x - r1.x) (r2.y - r1.y) (r2.z - r1.z) /
        ((lengthOf r1.x r1.y r1.z + lengthOf r2.x r2.y r2.z +
          lengthOf (r2.x - r1.x) (r2.y - r1.y) (r2.z - r1.z)) / 2)) 0) := by
  simp only [izzoParams, geometry]

/-- The sign interval encloses the sign of the direction of motion when the interval of
`(r1 × r2) · k` lies above or below zero. -/
theorem signOf_sound {d : Interval} {r1 r2 k : V3} (hd : Contains d (dot (cross r1 r2) k))
    (h : 0 < d.lo ∨ d.hi < 0) :
    Encloses (signOf d) (motionSign r1 r2 k) ∧
      (motionSign r1 r2 k = 1 ∨ motionSign r1 r2 k = -1) := by
  unfold signOf motionSign
  by_cases hp : 0 < d.lo
  · have := hd.pos_of_lo hp
    simp only [hp, this, ↓reduceIte]
    exact ⟨oneI_encloses, by norm_num⟩
  · have := hd.neg_of_hi (h.resolve_left hp)
    simp only [hp, not_lt.mpr this.le, ↓reduceIte]
    exact ⟨neg_oneI_encloses, by norm_num⟩

/-- **L4.**  For a result of `lambertBox` with status 0 and every input in the boxes, Izzo's `λ`
lies strictly between -1 and 1, `T` is positive, and the intervals contain the root of
`tof λ x = T` and Izzo's velocities at it. -/
theorem lambertBox_sound {x1 y1 z1 x2 y2 z2 t mu : Interval} {kx ky kz : Float}
    (hs : (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz).status = 0) {r1 r2 : V3} {t' μ : ℝ}
    (b1 : InBox x1 y1 z1 r1) (b2 : InBox x2 y2 z2 r2) (ht : Contains t t')
    (hμ : Contains mu μ) :
    -1 < (izzoParams r1 r2 t' μ ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩).1 ∧
      (izzoParams r1 r2 t' μ ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩).1 < 1 ∧
      0 < (izzoParams r1 r2 t' μ ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩).2 ∧
      Inside (lambertBox x1 y1 z1 x2 y2 z2 t mu kx ky kz)
        (solution r1 r2 t' μ ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩) := by
  have hd := direction.encloses (powLog := noTable) (powExp := noTable)
    b1.encloses.1 b1.encloses.2.1 b1.encloses.2.2 b2.encloses.1 b2.encloses.2.1
    b2.encloses.2.2 (point_encloses kx) (point_encloses ky) (point_encloses kz)
  rw [← directionI_tables, direction_eq'] at hd
  unfold lambertBox lambertBoxWith at hs ⊢
  dsimp only at hs ⊢
  generalize directionI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 (point kx) (point ky)
    (point kz) = d at hd hs ⊢
  generalize (⟨value kx.toBits, value ky.toBits, value kz.toBits⟩ : V3) = k at hd ⊢
  have hgeo := fun (h : Encloses (signOf d) (motionSign r1 r2 k)) =>
    geometry.encloses (powLog := noTable) (powExp := noTable)
      b1.encloses.1 b1.encloses.2.1 b1.encloses.2.2 b2.encloses.1 b2.encloses.2.1
      b2.encloses.2.2 (fun _ => ht) (fun _ => hμ) h
  rw [← geometryI_tables] at hgeo
  generalize geometryI noTable noTable noTable noTable x1 y1 z1 x2 y2 z2 t mu (signOf d) = g
    at hgeo hs ⊢
  split_ifs at hs ⊢ with hv hp hdir hg hT
  · have cd := hd hdir.1
    have hD : dot (cross r1 r2) k ≠ 0 := by
      rcases hdir.2 with h | h
      · exact (cd.pos_of_lo h).ne'
      · exact (cd.neg_of_hi h).ne
    obtain ⟨hsgE, hsg2⟩ := signOf_sound cd hdir.2
    have hg' : g.1.status = 0 ∧ g.2.status = 0 := by simpa using hg
    have cl := (hgeo hsgE).1 hg'.1
    have cT := (hgeo hsgE).2 hg'.2
    have hT0 : 0 < (izzoParams r1 r2 t' μ k).2 := cT.pos_of_lo hT
    have hl : -1 < (izzoParams r1 r2 t' μ k).1 ∧ (izzoParams r1 r2 t' μ k).1 < 1 := by
      rw [izzoParams_fst]
      exact lam_bounds (lengthOf_nonneg r1.x r1.y r1.z) (lengthOf_nonneg r2.x r2.y r2.z)
        (chord_pos hD) hsg2
    exact ⟨hl.1, hl.2, hT0, solve_sound hs b1 b2 hμ hsgE cl cT hl.1 hl.2 hT0⟩
  all_goals simp [noTransfer] at hs

/-- **L4 on endpoints.** -/
theorem lambertBounds_sound {x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
    mulo muhi kx ky kz : Float} {r1 r2 : V3} {t' μ : ℝ}
    (hs : (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi mulo
      muhi kx ky kz).status = 0)
    (c1 : Between x1lo x1hi r1.x ∧ Between y1lo y1hi r1.y ∧ Between z1lo z1hi r1.z)
    (c2 : Between x2lo x2hi r2.x ∧ Between y2lo y2hi r2.y ∧ Between z2lo z2hi r2.z)
    (ct : Between tlo thi t') (cμ : Between mulo muhi μ) :
    -1 < (izzoParams r1 r2 t' μ ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩).1 ∧
      (izzoParams r1 r2 t' μ ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩).1 < 1 ∧
      0 < (izzoParams r1 r2 t' μ ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩).2 ∧
      Inside (lambertBounds x1lo x1hi y1lo y1hi z1lo z1hi x2lo x2hi y2lo y2hi z2lo z2hi tlo thi
        mulo muhi kx ky kz)
        (solution r1 r2 t' μ ⟨value kx.toBits, value ky.toBits, value kz.toBits⟩) := by
  have hin : (make x1lo x1hi).status = 0 ∧ (make y1lo y1hi).status = 0 ∧
      (make z1lo z1hi).status = 0 ∧ (make x2lo x2hi).status = 0 ∧ (make y2lo y2hi).status = 0 ∧
      (make z2lo z2hi).status = 0 ∧ (make tlo thi).status = 0 ∧ (make mulo muhi).status = 0 := by
    unfold lambertBounds lambertBoundsWith lambertBoxWith at hs
    dsimp only at hs
    split_ifs at hs with hv
    all_goals first
      | (simp only [Bool.and_eq_true] at hv
         obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨v1, v2⟩, v3⟩, v4⟩, v5⟩, v6⟩, v7⟩, v8⟩, -⟩, -⟩, -⟩ := hv
         exact ⟨valid_status v1, valid_status v2, valid_status v3, valid_status v4,
           valid_status v5, valid_status v6, valid_status v7, valid_status v8⟩)
      | simp [noTransfer] at hs
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hin
  unfold lambertBounds lambertBoundsWith at hs ⊢
  exact lambertBox_sound hs
    ⟨contains_make a1 c1.1, contains_make a2 c1.2.1, contains_make a3 c1.2.2⟩
    ⟨contains_make a4 c2.1, contains_make a5 c2.2.1, contains_make a6 c2.2.2⟩
    (contains_make a7 ct) (contains_make a8 cμ)

end Demos.Orbit
