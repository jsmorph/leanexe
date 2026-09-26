import Project.Drone.Kinematics

namespace Project.Drone.Gluing
noncomputable section
open Set Filter
open scoped Topology

def join (cut : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ := if t ≤ cut then f t else g t

/-- Matching values and derivatives suffice to glue two differentiable curves.
No equality of second derivatives is required. -/
theorem join_derivative (cut : ℝ) (f g df dg : ℝ → ℝ)
    (hf : ∀ t, HasDerivAt f (df t) t) (hg : ∀ t, HasDerivAt g (dg t) t)
    (hp : f cut = g cut) (hv : df cut = dg cut) (t : ℝ) :
    HasDerivAt (join cut f g) (join cut df dg t) t := by
  rcases lt_trichotomy t cut with ht | heq | ht
  · rw [join, if_pos (le_of_lt ht)]
    exact (hf t).congr_of_eventuallyEq ((gt_mem_nhds ht).mono fun u hu => by
      simp [join, le_of_lt hu])
  · subst t
    rw [join, if_pos le_rfl]
    have hl : HasDerivWithinAt (join cut f g) (df cut) (Iic cut) cut :=
      (hf cut).hasDerivWithinAt.congr
        (fun u hu => by change u ≤ cut at hu; simp [join, hu]) (by simp [join])
    have hr : HasDerivWithinAt (join cut f g) (df cut) (Ioi cut) cut := by
      rw [hv]
      exact (hg cut).hasDerivWithinAt.congr
        (fun u hu => by change cut < u at hu; simp [join, not_le.mpr hu])
        (by simpa [join] using hp)
    simpa only [Iic_union_Ioi, hasDerivWithinAt_univ] using hl.union hr
  · rw [join, if_neg (not_le.mpr ht)]
    exact (hg t).congr_of_eventuallyEq ((lt_mem_nhds ht).mono fun u hu => by
      simp [join, not_le.mpr hu])

theorem join_continuous (cut : ℝ) (f g : ℝ → ℝ) (hf : Continuous f)
    (hg : Continuous g) (hp : f cut = g cut) : Continuous (join cut f g) := by
  exact hf.if_le hg continuous_id continuous_const (fun t ht => by simpa [ht] using hp)

def clock (d : Nat → ℝ) : Nat → ℝ
  | 0 => 0
  | n+1 => clock d n + d n

/-- A finite sequence of local curves on one cumulative physical-time axis.
The final polynomial is extended beyond the flight interval; safety claims
will be restricted to the actual flight interval. -/
def stitch (initial : ℝ) (segments : Nat → ℝ → ℝ) (d : Nat → ℝ) : Nat → ℝ → ℝ
  | 0 => fun _ => initial
  | n+1 => join (clock d n) (stitch initial segments d n)
      (fun t => segments n (t-clock d n))

theorem stitch_end (initial : ℝ) (segments : Nat → ℝ → ℝ) (d : Nat → ℝ)
    (n : Nat) (hd : 0 < d n) :
    stitch initial segments d (n+1) (clock d (n+1)) = segments n (d n) := by
  simp [stitch, clock, join, show ¬clock d n + d n ≤ clock d n by linarith]

/-- Global differentiability and a continuous velocity for finitely many
segments whose endpoint positions and velocities match. -/
theorem stitch_smooth (p0 v0 : ℝ) (p v : Nat → ℝ → ℝ) (d : Nat → ℝ) (N : Nat)
    (hd : ∀ i, i < N → 0 < d i)
    (hp : ∀ i, i < N → ∀ t, HasDerivAt (p i) (v i t) t)
    (hc : ∀ i, i < N → Continuous (v i))
    (hfirst : 0 < N → p0 = p 0 0 ∧ v0 = v 0 0)
    (hjoin : ∀ i, i+1 < N → p i (d i) = p (i+1) 0 ∧ v i (d i) = v (i+1) 0)
    (hv0 : v0 = 0) :
    (∀ t, HasDerivAt (stitch p0 p d N) (stitch v0 v d N t) t) ∧
    Continuous (stitch v0 v d N) := by
  induction N with
  | zero =>
    constructor
    · intro t
      simpa [stitch, hv0] using hasDerivAt_const t p0
    · exact continuous_const
  | succ n ih =>
    have prev := ih (fun i hi => hd i (by omega)) (fun i hi => hp i (by omega))
      (fun i hi => hc i (by omega)) (fun hn => hfirst (by omega))
      (fun i hi => hjoin i (by omega))
    have hmatch : stitch p0 p d n (clock d n) = p n 0 ∧
        stitch v0 v d n (clock d n) = v n 0 := by
      cases n with
      | zero => simpa [stitch, clock] using hfirst (by omega)
      | succ k =>
        rw [stitch_end p0 p d k (hd k (by omega)), stitch_end v0 v d k (hd k (by omega))]
        exact hjoin k (by omega)
    have shifted : ∀ t, HasDerivAt (fun t => p n (t-clock d n)) (v n (t-clock d n)) t := by
      intro t
      simpa only [Function.comp_def, id_eq, mul_one] using
        (hp n (by omega) (t-clock d n)).comp t ((hasDerivAt_id t).sub_const (clock d n))
    constructor
    · intro t
      exact join_derivative _ _ _ _ _ prev.1 shifted
        (by simpa using hmatch.1) (by simpa using hmatch.2) t
    · exact join_continuous _ _ _ prev.2 ((hc n (by omega)).comp (continuous_id.sub continuous_const))
        (by simpa using hmatch.2)

theorem clock_mono (d : Nat → ℝ) (N : Nat) (hd : ∀ i, i < N → 0 ≤ d i)
    (i : Nat) (hi : i ≤ N) : clock d i ≤ clock d N := by
  induction N with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ n ih =>
    by_cases he : i = n+1
    · subst i; rfl
    · have hp := ih (fun j hj => hd j (by omega)) (by omega)
      have hn := hd n (by omega)
      simp only [clock]
      linarith

/-- Every local flight interval is represented by its intended primitive,
including both boundary instants. -/
theorem stitch_on_segment (p0 : ℝ) (p : Nat → ℝ → ℝ) (d : Nat → ℝ) (N : Nat)
    (hd : ∀ i, i < N → 0 < d i)
    (hfirst : 0 < N → p0 = p 0 0)
    (hjoin : ∀ i, i+1 < N → p i (d i) = p (i+1) 0)
    (i : Nat) (hi : i < N) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ d i) :
    stitch p0 p d N (clock d i+t) = p i t := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases he : i = n
    · subst i
      by_cases ht : t = 0
      · subst t
        simp only [add_zero, stitch, join, le_refl, ite_true]
        cases n with
        | zero => simpa [stitch] using hfirst (by omega)
        | succ k =>
          rw [stitch_end p0 p d k (hd k (by omega))]
          exact hjoin k (by omega)
      · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
        have hgt : ¬clock d n+t ≤ clock d n := by linarith
        simp [stitch, join, hgt]
    · have hin : i < n := by omega
      have hc := clock_mono d n (fun j hj => le_of_lt (hd j (by omega))) (i+1) (by omega)
      have ht : clock d i+t ≤ clock d n := by simp only [clock] at hc; linarith
      simp only [stitch, join, ht, ite_true]
      exact ih (fun j hj => hd j (by omega)) (fun hn => hfirst (by omega))
        (fun j hj => hjoin j (by omega)) hin

/-- The cumulative intervals cover every physical time during a nonempty flight. -/
theorem clock_cover (d : Nat → ℝ) (N : Nat) (hN : 0 < N)
    (hd : ∀ i, i < N → 0 < d i) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ clock d N) :
    ∃ i, i < N ∧ clock d i ≤ t ∧ t ≤ clock d i+d i := by
  induction N with
  | zero => omega
  | succ n ih =>
    by_cases ht : clock d n ≤ t
    · exact ⟨n, by omega, ht, by simpa [clock] using ht1⟩
    · have hn : 0 < n := by
        by_contra hn
        have : n = 0 := by omega
        subst n
        exact ht (by simpa [clock] using ht0)
      obtain ⟨i, hi, ha, hb⟩ := ih hn (fun j hj => hd j (by omega)) (le_of_lt (lt_of_not_ge ht))
      exact ⟨i, by omega, ha, hb⟩

#print axioms join_derivative
#print axioms stitch_smooth
#print axioms stitch_on_segment
#print axioms clock_cover
end
end Project.Drone.Gluing
