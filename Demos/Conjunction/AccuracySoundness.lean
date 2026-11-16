import Demos.Conjunction.Accuracy
import Demos.Conjunction.AccuracyModel
import Demos.Conjunction.Soundness

/-!
Soundness of the radius searches.  `circularError_sound` states that an accepted result of
`circularError` holds the radius of the disk about the origin whose probability `Model.pc` is `p`,
and `linearError_sound` that an accepted result of `linearError` holds the half-width whose
probability `Model.linearProb` is `p`.  The proofs follow the search for any enclosure `E` of a
probability `P`: the bracketing keeps a lower end whose probability `E` shows below `p` and, once
it ends, an upper end whose probability `E` shows at least `p`, and each bisection keeps one of
the two.  `Model.radiusIn_of` turns the two ends into the radius.  `guarded_sound` proves the input
tests and the exchange of axes of the circular error for any search that holds the radius, so that
`circularError_sound` and `circularErrorAdaptive_sound` of `AdaptiveSoundness.lean` share them.
-/

namespace Demos.Conjunction.Accuracy

open LeanExe.ProofKit Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open Demos.Conjunction
open CodeLib.IEEE64 (value Finite)

set_option exponentiation.threshold 4096

/-! ### Searches over any enclosure -/

/-- A finite radius `x ≥ 0` whose probability under `P` lies below `q`. -/
def Below (P : ℝ → ℝ) (q : ℝ) (x : Float) : Prop :=
  Finite x.toBits ∧ 0 ≤ value x.toBits ∧ P (value x.toBits) < q

/-- A finite radius `x ≥ 0` whose probability under `P` is at least `q`, with the facts `H`. -/
def Above (H : Prop) (P : ℝ → ℝ) (q : ℝ) (x : Float) : Prop :=
  H ∧ Finite x.toBits ∧ 0 ≤ value x.toBits ∧ q ≤ P (value x.toBits)

/-- `E` encloses `P`: an accepted `E r` belongs to a finite radius `r ≥ 0`, contains
`P (value r)`, and implies `H`. -/
def Encl (H : Prop) (E : Float → Interval) (P : ℝ → ℝ) : Prop :=
  ∀ r, (E r).status = 0 →
    H ∧ Finite r.toBits ∧ 0 ≤ value r.toBits ∧ Contains (E r) (P (value r.toBits))

def growWith (E : Float → Interval) (p s : Float) : Bracket :=
  LeanExe.loop 16 ⟨0, 0.0, s⟩ fun _ b => if b.found == 1 then b else growStep p b (E b.hi)

def raiseWith (E : Float → Interval) (p : Float) (k : UInt64) (g : Bracket) : Bracket :=
  LeanExe.loop k g fun _ e => raiseStep p e (middle e) (E (middle e))

def lowerWith (E : Float → Interval) (p : Float) (k : UInt64) (g : Bracket) : Bracket :=
  LeanExe.loop k g fun _ e => lowerStep p e (middle e) (E (middle e))

/-- The result of a search for an enclosure `E`, from the starting radius `s`. -/
def result (E : Float → Interval) (p s : Float) (k : UInt64) : Radius :=
  if (growWith E p s).found == 1 then
    ⟨0, (raiseWith E p k (growWith E p s)).lo, (lowerWith E p k (growWith E p s)).hi⟩
  else ⟨2, 0.0, 0.0⟩

theorem result_parts {E : Float → Interval} {p s : Float} {k : UInt64}
    (h : (result E p s k).status = 0) :
    (growWith E p s).found = 1 ∧ (result E p s k).lo = (raiseWith E p k (growWith E p s)).lo ∧
      (result E p s k).hi = (lowerWith E p k (growWith E p s)).hi := by
  unfold result at h ⊢
  by_cases hf : (growWith E p s).found = 1
  · simp [hf]
  · simp [hf] at h

theorem loop_inv {α : Type} {n : UInt64} {init : α} {f : UInt64 → α → α} (I : α → Prop)
    (h0 : I init) (hs : ∀ i s, I s → I (f i s)) : I (LeanExe.loop n init f) :=
  LeanExe.Dialect.loop_induction (fun _ s => I s) h0 fun _ s _ h => hs _ s h

theorem status_true {e : Interval} (h : e.status = 0) : (e.status == 0) = true := by
  simp [h]

theorem status_false {e : Interval} (h : ¬ e.status = 0) : ¬ (e.status == 0) = true := by
  simp [h]

variable {H : Prop} {E : Float → Interval} {P : ℝ → ℝ} {p : Float}

theorem growStep_inv (hE : Encl H E P) (hp : Finite p.toBits) {b : Bracket}
    (hb : Below P (value p.toBits) b.lo) :
    Below P (value p.toBits) (growStep p b (E b.hi)).lo ∧
      ((growStep p b (E b.hi)).found = 1 → Above H P (value p.toBits) (growStep p b (E b.hi)).hi) := by
  unfold growStep
  by_cases hs : (E b.hi).status = 0
  · obtain ⟨hH, fr, hr0, hc⟩ := hE b.hi hs
    rw [ite_eq_left (status_true hs)]
    by_cases g1 : p ≤ (E b.hi).lo
    · rw [ite_eq_left g1]
      exact ⟨hb, fun _ => ⟨hH, fr, hr0, ((le_iff_value hp hc.2.1).mp g1).trans hc.2.2.2.1⟩⟩
    · rw [ite_eq_right g1]
      by_cases g2 : (E b.hi).hi < p
      · rw [ite_eq_left g2]
        exact ⟨⟨fr, hr0, lt_of_le_of_lt hc.2.2.2.2 ((lt_iff_value hc.2.2.1 hp).mp g2)⟩,
          fun h => absurd (show (0 : UInt64) = 1 from h) (by decide)⟩
      · rw [ite_eq_right g2]
        exact ⟨hb, fun h => absurd (show (0 : UInt64) = 1 from h) (by decide)⟩
  · rw [ite_eq_right (status_false hs)]
    exact ⟨hb, fun h => absurd (show (0 : UInt64) = 1 from h) (by decide)⟩

theorem raiseStep_below (hE : Encl H E P) (hp : Finite p.toBits) {b : Bracket} (mid : Float)
    (hb : Below P (value p.toBits) b.lo) :
    Below P (value p.toBits) (raiseStep p b mid (E mid)).lo := by
  unfold raiseStep
  by_cases hs : (E mid).status = 0
  · obtain ⟨-, fr, hr0, hc⟩ := hE mid hs
    rw [ite_eq_left (status_true hs)]
    by_cases g : (E mid).hi < p
    · rw [ite_eq_left g]
      exact ⟨fr, hr0, lt_of_le_of_lt hc.2.2.2.2 ((lt_iff_value hc.2.2.1 hp).mp g)⟩
    · rw [ite_eq_right g]
      exact hb
  · rw [ite_eq_right (status_false hs)]
    exact hb

theorem lowerStep_above (hE : Encl H E P) (hp : Finite p.toBits) {b : Bracket} (mid : Float)
    (hb : Above H P (value p.toBits) b.hi) :
    Above H P (value p.toBits) (lowerStep p b mid (E mid)).hi := by
  unfold lowerStep
  by_cases hs : (E mid).status = 0
  · obtain ⟨hH, fr, hr0, hc⟩ := hE mid hs
    rw [ite_eq_left (status_true hs)]
    by_cases g : p ≤ (E mid).lo
    · rw [ite_eq_left g]
      exact ⟨hH, fr, hr0, ((le_iff_value hp hc.2.1).mp g).trans hc.2.2.2.1⟩
    · rw [ite_eq_right g]
      exact hb
  · rw [ite_eq_right (status_false hs)]
    exact hb

/-- The bracketing keeps a lower end below `p`, and an upper end at least `p` once it ends. -/
theorem growWith_inv (hE : Encl H E P) (hp : Finite p.toBits) (hq : 0 < value p.toBits)
    (hP0 : P 0 = 0) (s : Float) :
    Below P (value p.toBits) (growWith E p s).lo ∧
      ((growWith E p s).found = 1 → Above H P (value p.toBits) (growWith E p s).hi) := by
  unfold growWith
  refine loop_inv (fun b : Bracket => Below P (value p.toBits) b.lo ∧
    (b.found = 1 → Above H P (value p.toBits) b.hi)) ?_ ?_
  · refine ⟨⟨lit_zero.1, by rw [lit_zero.2], by rw [lit_zero.2, hP0]; exact hq⟩,
      fun h => absurd (show (0 : UInt64) = 1 from h) (by decide)⟩
  · intro _ b hb
    by_cases hf : (b.found == 1) = true
    · rw [ite_eq_left hf]
      exact hb
    · rw [ite_eq_right hf]
      exact growStep_inv hE hp hb.1

theorem raiseWith_below (hE : Encl H E P) (hp : Finite p.toBits) (k : UInt64) {g : Bracket}
    (hg : Below P (value p.toBits) g.lo) : Below P (value p.toBits) (raiseWith E p k g).lo :=
  loop_inv (fun e : Bracket => Below P (value p.toBits) e.lo) hg
    fun _ e he => raiseStep_below hE hp (middle e) he

theorem lowerWith_above (hE : Encl H E P) (hp : Finite p.toBits) (k : UInt64) {g : Bracket}
    (hg : Above H P (value p.toBits) g.hi) : Above H P (value p.toBits) (lowerWith E p k g).hi :=
  loop_inv (fun e : Bracket => Above H P (value p.toBits) e.hi) hg
    fun _ e he => lowerStep_above hE hp (middle e) he

/-- An accepted search: the lower end of the first bisection and the upper end of the second hold
the radius of probability `p`, for a probability that is zero at zero and, under `H`,
continuous and strictly increasing on `[0, ∞)`. -/
theorem search_sound (hE : Encl H E P) (hp : Finite p.toBits) (hq : 0 < value p.toBits)
    (hP0 : P 0 = 0) (hm : H → StrictMonoOn P (Set.Ici 0))
    (hcont : H → ContinuousOn P (Set.Ici 0)) {s : Float} (k : UInt64)
    (hf : (growWith E p s).found = 1) :
    H ∧ Finite (raiseWith E p k (growWith E p s)).lo.toBits ∧
      Finite (lowerWith E p k (growWith E p s)).hi.toBits ∧
      Model.RadiusIn P (value p.toBits) (value (raiseWith E p k (growWith E p s)).lo.toBits)
        (value (lowerWith E p k (growWith E p s)).hi.toBits) := by
  obtain ⟨hlo, hhi⟩ := growWith_inv hE hp hq hP0 s
  have ha := raiseWith_below hE hp k hlo
  have hc := lowerWith_above hE hp k (hhi hf)
  exact ⟨hc.1, ha.1, hc.2.1, Model.radiusIn_of (hm hc.1) (hcont hc.1) ha.2.1 hc.2.2.1 ha.2.2
    hc.2.2.2⟩

/-! ### The circular error -/

/-- An accepted `pcWith` with the table of `exp` belongs to a finite radius. -/
theorem pcWith_radius_finite {m1 m2 c11 c12 c22 r : Float} {n : UInt64}
    (h : (pcWith Exp.expTable m1 m2 c11 c12 c22 r n).status = 0) : Finite r.toBits := by
  obtain ⟨hc, -, -, -⟩ := pcWith_enclosure h
  unfold pcWith at h
  by_cases g1 : (0.0 : Float) < c11
  · by_cases g2 : (0.0 : Float) < r
    · by_cases g3 : 1 ≤ n
      · by_cases g4 : n ≤ 1048576
        · simp only [g1, g2, g3, g4, ite_true] at h
          obtain ⟨s0, -⟩ := clamp_sound h
          obtain ⟨-, s2, -⟩ := mul_sound s0
          have hr : Finite r.toBits → 0 < value r.toBits := fun fr => by
            have := (lt_iff_value lit_zero.1 fr).mp g2
            rwa [lit_zero.2] at this
          exact (panels_sound hc hr g3 s2).1
        · simp only [g1, g2, g3, g4, ite_true, ite_false] at h
          exact absurd h (by decide)
      · simp only [g1, g2, g3, ite_true, ite_false] at h
        exact absurd h (by decide)
    · simp only [g1, g2, ite_true, ite_false] at h
      exact absurd h (by decide)
  · simp only [g1, ite_false] at h
    exact absurd h (by decide)

/-- `pcWith` with the table of `exp` encloses the probability of the disk. -/
theorem disk_encl (m1 m2 c11 c12 c22 : Float) (n : UInt64) :
    Encl (0 < value c11.toBits ∧
        0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits))
      (fun r => pcWith Exp.expTable m1 m2 c11 c12 c22 r n)
      (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits) (value c12.toBits)
        (value c22.toBits)) := by
  intro r h
  obtain ⟨hc, hd, hr, hcont, -⟩ := pcWith_enclosure h
  exact ⟨⟨hc, hd⟩, pcWith_radius_finite h, hr.le, hcont⟩

theorem diskSearch_eq (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) :
    diskSearch tab m1 m2 c11 c12 c22 p n k =
      result (fun r => pcWith tab m1 m2 c11 c12 c22 r n) p
        (Float.sqrt (c11 + c22) + Float.sqrt (m1 * m1 + m2 * m2)) k := rfl

theorem diskSearch_sound {m1 m2 c11 c12 c22 p : Float} {n k : UInt64} (hp : Finite p.toBits)
    (hq : 0 < value p.toBits) (h : (diskSearch Exp.expTable m1 m2 c11 c12 c22 p n k).status = 0) :
    (0 < value c11.toBits ∧
        0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits)) ∧
      Finite (diskSearch Exp.expTable m1 m2 c11 c12 c22 p n k).lo.toBits ∧
      Finite (diskSearch Exp.expTable m1 m2 c11 c12 c22 p n k).hi.toBits ∧
      Model.RadiusIn (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits)
          (value c12.toBits) (value c22.toBits)) (value p.toBits)
        (value (diskSearch Exp.expTable m1 m2 c11 c12 c22 p n k).lo.toBits)
        (value (diskSearch Exp.expTable m1 m2 c11 c12 c22 p n k).hi.toBits) := by
  rw [diskSearch_eq] at h ⊢
  obtain ⟨hf, hlo, hhi⟩ := result_parts h
  rw [hlo, hhi]
  exact search_sound (disk_encl m1 m2 c11 c12 c22 n) hp hq (Model.pc_zero _ _ _ _ _)
    (fun hH => Model.pc_strictMonoOn _ _ _ _ _ hH.2)
    (fun hH => Model.pc_continuousOn _ _ _ _ _ hH.1 hH.2) k hf

/-- The input tests of `circularErrorWith`, with the least number of panels `nmin`, around a
search `S` that receives the mean, the covariance, and the probability after the exchange of
axes. -/
def guarded (nmin : UInt64) (S : Float → Float → Float → Float → Float → Float → Radius)
    (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : Radius :=
  if finite m1 && finite m2 && finite c11 && finite c12 && finite c22 && finite p then
    if 0.0 < p ∧ p < 1.0 ∧ 0.0 < c11 ∧ 0.0 < c22 ∧ nmin ≤ n ∧ n ≤ 1048576 ∧ k ≤ 64 then
      if c22 ≤ c11 then
        if definite c11 c12 c22 then S m1 m2 c11 c12 c22 p else ⟨1, 0.0, 0.0⟩
      else if definite c22 c12 c11 then S m2 m1 c22 c12 c11 p
      else ⟨1, 0.0, 0.0⟩
    else ⟨1, 0.0, 0.0⟩
  else ⟨1, 0.0, 0.0⟩

theorem circularErrorWith_eq (tab : Array UInt64) (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) :
    circularErrorWith tab m1 m2 c11 c12 c22 p n k =
      guarded 1 (fun a b c d e q => diskSearch tab a b c d e q n k) m1 m2 c11 c12 c22 p n k :=
  rfl

/-- An accepted result of the input tests around a search `S` holds the radius of the disk about
the origin whose probability is `p`, when every accepted result of `S` for a probability above 0
holds that radius for its arguments. -/
theorem guarded_sound {nmin : UInt64} {S : Float → Float → Float → Float → Float → Float → Radius}
    (hS : ∀ a b c d e q : Float, Finite q.toBits → 0 < value q.toBits →
      (S a b c d e q).status = 0 →
        (0 < value c.toBits ∧ 0 < Model.det (value c.toBits) (value d.toBits) (value e.toBits)) ∧
        Finite (S a b c d e q).lo.toBits ∧ Finite (S a b c d e q).hi.toBits ∧
        Model.RadiusIn (Model.pc (value a.toBits) (value b.toBits) (value c.toBits)
            (value d.toBits) (value e.toBits)) (value q.toBits)
          (value (S a b c d e q).lo.toBits) (value (S a b c d e q).hi.toBits))
    {m1 m2 c11 c12 c22 p : Float} {n k : UInt64}
    (h : (guarded nmin S m1 m2 c11 c12 c22 p n k).status = 0) :
    0 < value p.toBits ∧ value p.toBits < 1 ∧ 0 < value c11.toBits ∧
      0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
      Finite (guarded nmin S m1 m2 c11 c12 c22 p n k).lo.toBits ∧
      Finite (guarded nmin S m1 m2 c11 c12 c22 p n k).hi.toBits ∧
      Model.RadiusIn (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits)
          (value c12.toBits) (value c22.toBits)) (value p.toBits)
        (value (guarded nmin S m1 m2 c11 c12 c22 p n k).lo.toBits)
        (value (guarded nmin S m1 m2 c11 c12 c22 p n k).hi.toBits) := by
  unfold guarded at h ⊢
  by_cases g1 : (finite m1 && finite m2 && finite c11 && finite c12 && finite c22 && finite p) = true
  · rw [ite_eq_left g1] at h ⊢
    simp only [Bool.and_eq_true, finite_iff] at g1
    obtain ⟨⟨⟨⟨⟨-, -⟩, fc11⟩, -⟩, -⟩, fp⟩ := g1
    by_cases g2 : (0.0 : Float) < p ∧ p < 1.0 ∧ (0.0 : Float) < c11 ∧ (0.0 : Float) < c22 ∧
        nmin ≤ n ∧ n ≤ 1048576 ∧ k ≤ 64
    · rw [ite_eq_left g2] at h ⊢
      have hq : 0 < value p.toBits := by
        have := (lt_iff_value lit_zero.1 fp).mp g2.1
        rwa [lit_zero.2] at this
      have hq1 : value p.toBits < 1 := by
        have := (lt_iff_value fp lit_one.1).mp g2.2.1
        rwa [lit_one.2] at this
      have hc11 : 0 < value c11.toBits := by
        have := (lt_iff_value lit_zero.1 fc11).mp g2.2.2.1
        rwa [lit_zero.2] at this
      by_cases g3 : c22 ≤ c11
      · rw [ite_eq_left g3] at h ⊢
        by_cases g4 : definite c11 c12 c22 = true
        · rw [ite_eq_left g4] at h ⊢
          obtain ⟨⟨-, hd⟩, fl, fh, hR⟩ := hS _ _ _ _ _ _ fp hq h
          exact ⟨hq, hq1, hc11, hd, fl, fh, hR⟩
        · rw [ite_eq_right g4] at h
          exact absurd h (by decide)
      · rw [ite_eq_right g3] at h ⊢
        by_cases g4 : definite c22 c12 c11 = true
        · rw [ite_eq_left g4] at h ⊢
          obtain ⟨⟨-, hd⟩, fl, fh, hR⟩ := hS _ _ _ _ _ _ fp hq h
          have hdet : Model.det (value c22.toBits) (value c12.toBits) (value c11.toBits) =
              Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) := by
            unfold Model.det
            ring
          have hswap : Model.pc (value m2.toBits) (value m1.toBits) (value c22.toBits)
                (value c12.toBits) (value c11.toBits) =
              Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits) (value c12.toBits)
                (value c22.toBits) :=
            funext fun R => (Model.pc_swap _ _ _ _ _ R).symm
          rw [hdet] at hd
          rw [hswap] at hR
          exact ⟨hq, hq1, hc11, hd, fl, fh, hR⟩
        · rw [ite_eq_right g4] at h
          exact absurd h (by decide)
    · rw [ite_eq_right g2] at h
      exact absurd h (by decide)
  · rw [ite_eq_right g1] at h
    exact absurd h (by decide)

/-- An accepted result of `circularError` holds the radius of the disk about the origin whose
probability is `p`, for the real values of the inputs, whose covariance is positive definite. -/
theorem circularError_sound {m1 m2 c11 c12 c22 p : Float} {n k : UInt64}
    (h : (circularError m1 m2 c11 c12 c22 p n k).status = 0) :
    0 < value p.toBits ∧ value p.toBits < 1 ∧ 0 < value c11.toBits ∧
      0 < Model.det (value c11.toBits) (value c12.toBits) (value c22.toBits) ∧
      Finite (circularError m1 m2 c11 c12 c22 p n k).lo.toBits ∧
      Finite (circularError m1 m2 c11 c12 c22 p n k).hi.toBits ∧
      Model.RadiusIn (Model.pc (value m1.toBits) (value m2.toBits) (value c11.toBits)
          (value c12.toBits) (value c22.toBits)) (value p.toBits)
        (value (circularError m1 m2 c11 c12 c22 p n k).lo.toBits)
        (value (circularError m1 m2 c11 c12 c22 p n k).hi.toBits) := by
  rw [circularError, circularErrorWith_eq] at h ⊢
  exact guarded_sound (fun _ _ _ _ _ _ hp hq hs => diskSearch_sound hp hq hs) h

/-! ### The linear error -/

theorem half_bits : (0.5 : Float).toBits = 0x3FE0000000000000 := by decide +kernel

theorem lit_half : Finite (0.5 : Float).toBits ∧ value (0.5 : Float).toBits = 1 / 2 := by
  have hs : Wasm.IEEE64.scaledValue 0x3FE0000000000000 = 2 ^ 1073 := by decide +kernel
  refine ⟨?_, ?_⟩
  · rw [half_bits]; unfold CodeLib.IEEE64.Finite; decide +kernel
  · simp only [half_bits, value, hs]; push_cast; norm_num

/-- An accepted `lineScale v` contains `√v · √2`. -/
theorem lineScale_sound {v : Float} (h : (lineScale v).status = 0) :
    Contains (lineScale v) (Real.sqrt (value v.toBits) * Real.sqrt 2) := by
  unfold lineScale at h ⊢
  obtain ⟨s1, s2, hm⟩ := mul_sound h
  obtain ⟨s3, hq1⟩ := sqrt_sound s1
  obtain ⟨s4, hq2⟩ := sqrt_sound s2
  exact hm _ _ (hq1 _ (point_sound s3).2).2 (hq2 _ (point_lit lit_two s4)).2

/-- `lineAt` with the table of `exp` and the interval of `√v · √2` encloses the probability of
`[-L, L]`, for a positive variance. -/
theorem line_encl (b v : Float) (hv : 0 < value v.toBits) :
    Encl True (fun L => lineAt Exp.expTable b (lineScale v) L)
      (Model.linearProb (value b.toBits) (value v.toBits)) := by
  intro L h
  simp only [lineAt] at h ⊢
  by_cases g : (0.0 : Float) ≤ L
  · rw [ite_eq_left g] at h ⊢
    obtain ⟨s1, s2, hm⟩ := mul_sound h
    obtain ⟨s3, s4, ha⟩ := add_sound s2
    obtain ⟨s5, he1⟩ := erfI_sound s3
    obtain ⟨s6, he2⟩ := erfI_sound s4
    obtain ⟨s7, s8, hd1⟩ := div_sound s5
    obtain ⟨s9, -, hd2⟩ := div_sound s6
    obtain ⟨s10, s11, hs⟩ := sub_sound s7
    obtain ⟨-, -, hadd⟩ := add_sound s9
    obtain ⟨fL, cL⟩ := point_sound s10
    have cb := (point_sound s11).2
    have ck := lineScale_sound s8
    have hL : 0 ≤ value L.toBits := by
      have := (le_iff_value lit_zero.1 fL).mp g
      rwa [lit_zero.2] at this
    have c1 := (hd1 _ _ (hs _ _ cL cb) ck).2
    have c2 := (hd2 _ _ (hadd _ _ cL cb) ck).2
    have c3 := hm _ _ (point_lit lit_half s1) (ha _ _ (he1 _ c1) (he2 _ c2))
    refine ⟨trivial, fL, hL, ?_⟩
    rw [Model.linearProb_eq _ _ _ hv hL]
    exact c3
  · rw [ite_eq_right g] at h
    exact absurd h (by decide)

theorem lineSearch_eq (tab : Array UInt64) (b v : Float) (kap : Interval) (p : Float)
    (k : UInt64) :
    lineSearch tab b v kap p k =
      result (fun L => lineAt tab b kap L) p (Float.sqrt v + Float.abs b) k := rfl

/-- An accepted result of `linearError` holds the half-width of the interval about the origin
whose probability is `p`, for the real values of the inputs, whose variance is positive. -/
theorem linearError_sound {b v p : Float} {k : UInt64} (h : (linearError b v p k).status = 0) :
    0 < value p.toBits ∧ value p.toBits < 1 ∧ 0 < value v.toBits ∧
      Finite (linearError b v p k).lo.toBits ∧ Finite (linearError b v p k).hi.toBits ∧
      Model.RadiusIn (Model.linearProb (value b.toBits) (value v.toBits)) (value p.toBits)
        (value (linearError b v p k).lo.toBits) (value (linearError b v p k).hi.toBits) := by
  unfold linearError linearErrorWith at h ⊢
  by_cases g1 : (finite b && finite v && finite p) = true
  · rw [ite_eq_left g1] at h ⊢
    simp only [Bool.and_eq_true, finite_iff] at g1
    obtain ⟨⟨-, fv⟩, fp⟩ := g1
    by_cases g2 : (0.0 : Float) < p ∧ p < 1.0 ∧ (0.0 : Float) < v ∧ k ≤ 64
    · rw [ite_eq_left g2] at h ⊢
      have hq : 0 < value p.toBits := by
        have := (lt_iff_value lit_zero.1 fp).mp g2.1
        rwa [lit_zero.2] at this
      have hq1 : value p.toBits < 1 := by
        have := (lt_iff_value fp lit_one.1).mp g2.2.1
        rwa [lit_one.2] at this
      have hv : 0 < value v.toBits := by
        have := (lt_iff_value lit_zero.1 fv).mp g2.2.2.1
        rwa [lit_zero.2] at this
      simp only at h ⊢
      by_cases g3 : ((lineScale v).status == 0 && 0.0 < (lineScale v).lo) = true
      · rw [ite_eq_left g3] at h ⊢
        rw [lineSearch_eq] at h ⊢
        obtain ⟨hf, hlo, hhi⟩ := result_parts h
        rw [hlo, hhi]
        obtain ⟨-, fl, fh, hR⟩ := search_sound (line_encl b v hv) fp hq
          (Model.linearProb_zero _ _) (fun _ => Model.linearProb_strictMonoOn _ _ hv)
          (fun _ => Model.linearProb_continuousOn _ _ hv) k hf
        exact ⟨hq, hq1, hv, fl, fh, hR⟩
      · rw [ite_eq_right g3] at h
        exact absurd h (by decide)
    · rw [ite_eq_right g2] at h
      exact absurd h (by decide)
  · rw [ite_eq_right g1] at h
    exact absurd h (by decide)

#print axioms circularError_sound
#print axioms linearError_sound

end Demos.Conjunction.Accuracy
