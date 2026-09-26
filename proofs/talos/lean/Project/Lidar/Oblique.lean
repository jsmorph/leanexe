import LeanExe.Examples.LidarOblique
import Project.Lidar.Continuous
import Mathlib.Tactic.Ring

namespace Project.Lidar.Oblique
open LeanExe.Examples.Lidar LeanExe.Examples.LidarOblique
open Project.Lidar.Continuous

/-- Continuous rectangle membership in the exact tick parameterization. -/
def PositiveHit (b : Rect) (x y : Nat) (ticks : ℝ) : Prop :=
  100 * (b.x0 : ℝ) ≤ 100*x+ticks ∧ 100*(x : ℝ)+ticks ≤ 100*b.x1 ∧
  75 * (b.y0 : ℝ) ≤ 75*y+ticks ∧ 75*(y : ℝ)+ticks ≤ 75*b.y1

theorem scaled_lower (lo origin scale : Nat) (t : ℝ) (ht : 0 ≤ t)
    (h : (scale : ℝ)*lo ≤ (scale : ℝ)*origin+t) :
    ((scale*(lo-origin) : Nat) : ℝ) ≤ t := by
  by_cases ho : origin ≤ lo
  · rw [Nat.cast_mul, Nat.cast_sub ho]
    nlinarith
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    simpa using ht

theorem positive_first (b : Rect) (x y range : Nat) :
    Continuous.FirstHit (PositiveHit b x y) range (positiveDistance b x y range) := by
  have entered : (100*(b.x0-x) ≤ entry b x y) ∧ (75*(b.y0-y) ≤ entry b x y) :=
    ⟨Nat.le_max_left _ _, Nat.le_max_right _ _⟩
  refine ⟨?_, ?_, ?_⟩
  · unfold positiveDistance
    split <;> omega
  · intro hr
    by_cases h : x ≤ b.x1 ∧ y ≤ b.y1 ∧ entry b x y ≤ exit b x y ∧ entry b x y ≤ range
    · simp only [positiveDistance, if_pos h]
      have ex := Nat.le_trans h.2.2.1 (Nat.min_le_left _ _)
      have ey := Nat.le_trans h.2.2.1 (Nat.min_le_right _ _)
      have hx : 100*b.x0 ≤ 100*x+entry b x y ∧ 100*x+entry b x y ≤ 100*b.x1 := by
        omega
      have hy : 75*b.y0 ≤ 75*y+entry b x y ∧ 75*y+entry b x y ≤ 75*b.y1 := by
        omega
      unfold PositiveHit
      exact_mod_cast And.intro hx.1 (And.intro hx.2 hy)
    · simp only [positiveDistance, if_neg h] at hr
      omega
  · intro t ht hr hit
    rcases hit with ⟨hx0,hx1,hy0,hy1⟩
    have hx : x ≤ b.x1 := by
      have : (x : ℝ) ≤ b.x1 := by linarith
      exact_mod_cast this
    have hy : y ≤ b.y1 := by
      have : (y : ℝ) ≤ b.y1 := by linarith
      exact_mod_cast this
    have ex := scaled_lower b.x0 x 100 t ht hx0
    have ey := scaled_lower b.y0 y 75 t ht hy0
    have ent : (entry b x y : ℝ) ≤ t := by
      unfold entry
      exact_mod_cast max_le ex ey
    have tx : t ≤ ((100*(b.x1-x) : Nat) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hx]
      norm_num
      linarith
    have ty : t ≤ ((75*(b.y1-y) : Nat) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hy]
      norm_num
      linarith
    have exn : entry b x y ≤ 100*(b.x1-x) := by exact_mod_cast le_trans ent tx
    have eyn : entry b x y ≤ 75*(b.y1-y) := by exact_mod_cast le_trans ent ty
    have ern : entry b x y ≤ range := by exact_mod_cast le_trans ent hr
    have good : entry b x y ≤ exit b x y := Nat.le_min_of_le_of_le exn eyn
    simpa [positiveDistance, hx, hy, good, ern] using ent

def BoxHit (b : Rect) (x y direction : Nat) (ticks : ℝ) : Prop :=
  PositiveHit (reflected b direction) (originX x direction) (originY y direction) ticks

noncomputable def velocityX (direction : Nat) : ℝ :=
  if direction = 1 ∨ direction = 3 then -(3/5) else 3/5

noncomputable def velocityY (direction : Nat) : ℝ :=
  if direction = 2 ∨ direction = 3 then -(4/5) else 4/5

theorem unit_direction (direction : Nat) :
    velocityX direction ^ 2 + velocityY direction ^ 2 = 1 := by
  unfold velocityX velocityY
  split <;> split <;> norm_num

/-- Ordinary Cartesian membership, with `distance` in Euclidean distance units. -/
def GeometricHit (b : Rect) (x y direction : Nat) (distance : ℝ) : Prop :=
  (b.x0 : ℝ) ≤ x + velocityX direction*distance ∧
    (x : ℝ) + velocityX direction*distance ≤ b.x1 ∧
    (b.y0 : ℝ) ≤ y + velocityY direction*distance ∧
    (y : ℝ) + velocityY direction*distance ≤ b.y1

theorem geometric_iff (b : Rect) (x y direction : Nat) (distance : ℝ)
    (hb : b.Valid) (hx : x ≤ world) (hy : y ≤ world) (hd : direction < 4) :
    BoxHit b x y direction (60*distance) ↔ GeometricHit b x y direction distance := by
  have hx0 : b.x0 ≤ world := by rcases hb with ⟨_,_,_,_⟩; omega
  have hy0 : b.y0 ≤ world := by rcases hb with ⟨_,_,_,_⟩; omega
  have hx1 := hb.2.1
  have hy1 := hb.2.2.2
  have dirs : direction = 0 ∨ direction = 1 ∨ direction = 2 ∨ direction = 3 := by omega
  rcases dirs with rfl | rfl | rfl | rfl <;>
    norm_num [BoxHit, PositiveHit, reflected, originX, originY,
      GeometricHit, velocityX, velocityY, Nat.cast_sub hx, Nat.cast_sub hy,
      Nat.cast_sub hx0, Nat.cast_sub hy0, Nat.cast_sub hx1, Nat.cast_sub hy1]
  all_goals
    constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem trace_first (boxes : List Rect) (x y direction range : Nat) :
    Continuous.FirstHit (fun t => ∃ b ∈ boxes, BoxHit b x y direction t) range
      (LeanExe.Examples.LidarOblique.trace boxes x y direction range) := by
  induction boxes with
  | nil => simp [LeanExe.Examples.LidarOblique.trace, Continuous.FirstHit]
  | cons b rest ih =>
    have hb := positive_first (reflected b direction) (originX x direction) (originY y direction) range
    simpa [LeanExe.Examples.LidarOblique.trace, LeanExe.Examples.LidarOblique.boxDistance,
      BoxHit, List.mem_cons, or_and_right, exists_or, exists_eq_left] using Continuous.first_min hb ih

/-- The exact tick answer is the first intersection of a unit-speed Cartesian
ray. Dividing the parameter by 60 converts both range and answer to distance. -/
theorem geometric_first (boxes : List Rect) (x y direction range : Nat)
    (valid : ∀ b ∈ boxes, b.Valid) (hx : x ≤ world) (hy : y ≤ world)
    (hd : direction < 4) :
    Continuous.FirstHit (fun ticks => ∃ b ∈ boxes, GeometricHit b x y direction (ticks/60)) range
      (LeanExe.Examples.LidarOblique.trace boxes x y direction range) := by
  have h := trace_first boxes x y direction range
  have scale (t : ℝ) : 60*(t/60) = t := by ring
  refine ⟨h.1, ?_, ?_⟩
  · intro ha
    obtain ⟨b,hb,hit⟩ := h.2.1 ha
    refine ⟨b,hb,?_⟩
    apply (geometric_iff b x y direction _ (valid b hb) hx hy hd).1
    simpa only [scale] using hit
  · intro ticks ht hr hit
    obtain ⟨b,hb,hit⟩ := hit
    apply h.2.2 ticks ht hr
    refine ⟨b,hb,?_⟩
    have scaled := (geometric_iff b x y direction (ticks/60) (valid b hb) hx hy hd).2 hit
    simpa only [scale] using scaled

#print axioms trace_first
#print axioms geometric_first
end Project.Lidar.Oblique
