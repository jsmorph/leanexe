import Project.Lidar.Cardinal
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace Project.Lidar.Continuous
open LeanExe.Examples.Lidar

/-- Continuous geometric membership; time is a real distance along a unit
cardinal ray, even though rectangle corners and the answer are integral. -/
def AxisHit (lo hi low high origin transverse : Nat) (t : ℝ) : Prop :=
  (low : ℝ) ≤ transverse ∧ (transverse : ℝ) ≤ high ∧
  (lo : ℝ) ≤ origin+t ∧ (origin : ℝ)+t ≤ hi

def FirstHit (hit : ℝ → Prop) (range answer : Nat) : Prop :=
  answer ≤ range+1 ∧ (answer ≤ range → hit answer) ∧
  ∀ t : ℝ, 0 ≤ t → t ≤ range → hit t → (answer : ℝ) ≤ t

theorem sub_lower (lo origin : Nat) (t : ℝ) (ht : 0 ≤ t)
    (h : (lo : ℝ) ≤ origin+t) : ((lo-origin : Nat) : ℝ) ≤ t := by
  by_cases ho : origin ≤ lo
  · rw [Nat.cast_sub ho]
    linarith
  · rw [Nat.sub_eq_zero_of_le (by omega)]
    simpa using ht

theorem axis_first (lo hi low high origin transverse range : Nat) (ordered : lo ≤ hi) :
    FirstHit (AxisHit lo hi low high origin transverse) range
      (axisDistance lo hi low high origin transverse range) := by
  have hn := Project.Lidar.axis_first lo hi low high origin transverse range ordered
  refine ⟨hn.1, ?_, ?_⟩
  · intro hr
    have hs := hn.2.1 hr
    unfold Project.Lidar.AxisHit at hs
    unfold AxisHit
    exact_mod_cast hs
  · intro t ht hr hit
    rcases hit with ⟨hlo,hhi,hentry,hexit⟩
    have hc0 : low ≤ transverse := by exact_mod_cast hlo
    have hc1 : transverse ≤ high := by exact_mod_cast hhi
    have hx : origin ≤ hi := by
      have : (origin : ℝ) ≤ hi := by linarith
      exact_mod_cast this
    have hd := sub_lower lo origin t ht hentry
    have hdist : lo-origin ≤ range := by
      have : ((lo-origin : Nat) : ℝ) ≤ range := le_trans hd hr
      exact_mod_cast this
    simpa [axisDistance, hc0, hc1, hx, hdist] using hd

theorem first_min {a b : ℝ → Prop} {range da db : Nat}
    (ha : FirstHit a range da) (hb : FirstHit b range db) :
    FirstHit (fun t => a t ∨ b t) range (min da db) := by
  rcases ha with ⟨ha0,ha1,ha2⟩
  rcases hb with ⟨hb0,hb1,hb2⟩
  by_cases h : da ≤ db
  · rw [Nat.min_eq_left h]
    refine ⟨ha0, fun hd => Or.inl (ha1 hd), ?_⟩
    intro t ht hr hit
    rcases hit with ha | hb
    · exact ha2 t ht hr ha
    · exact le_trans (by exact_mod_cast h) (hb2 t ht hr hb)
  · have h' : db ≤ da := by omega
    rw [Nat.min_eq_right h']
    refine ⟨hb0, fun hd => Or.inr (hb1 hd), ?_⟩
    intro t ht hr hit
    rcases hit with ha | hb
    · exact le_trans (by exact_mod_cast h') (ha2 t ht hr ha)
    · exact hb2 t ht hr hb

def BoxHit (b : Rect) (x y direction : Nat) (t : ℝ) : Prop :=
  if direction = 0 then AxisHit b.x0 b.x1 b.y0 b.y1 x y t
  else if direction = 1 then AxisHit (world-b.x1) (world-b.x0) b.y0 b.y1 (world-x) y t
  else if direction = 2 then AxisHit b.y0 b.y1 b.x0 b.x1 y x t
  else AxisHit (world-b.y1) (world-b.y0) b.x0 b.x1 (world-y) x t

/-- Ordinary Cartesian closed-rectangle membership of the actual ray. -/
def GeometricHit (b : Rect) (x y direction : Nat) (t : ℝ) : Prop :=
  let px : ℝ := if direction = 0 then x+t else if direction = 1 then x-t else x
  let py : ℝ := if direction = 2 then y+t else if direction = 3 then y-t else y
  (b.x0 : ℝ) ≤ px ∧ px ≤ b.x1 ∧ (b.y0 : ℝ) ≤ py ∧ py ≤ b.y1

theorem geometric_iff (b : Rect) (x y direction : Nat) (t : ℝ) (hb : b.Valid)
    (hx : x ≤ world) (hy : y ≤ world) (hd : direction < 4) :
    BoxHit b x y direction t ↔ GeometricHit b x y direction t := by
  have hx0 : b.x0 ≤ world := by rcases hb with ⟨_,_,_,_⟩; omega
  have hy0 : b.y0 ≤ world := by rcases hb with ⟨_,_,_,_⟩; omega
  have hx1 := hb.2.1
  have hy1 := hb.2.2.2
  have dirs : direction = 0 ∨ direction = 1 ∨ direction = 2 ∨ direction = 3 := by omega
  rcases dirs with rfl | rfl | rfl | rfl <;>
    simp only [BoxHit, GeometricHit, AxisHit, Nat.cast_sub hx, Nat.cast_sub hy,
      Nat.cast_sub hx0, Nat.cast_sub hy0, Nat.cast_sub hx1, Nat.cast_sub hy1] <;>
    norm_num only <;> simp only [ite_true, ite_false]
  all_goals
    constructor <;> rintro ⟨a,b,c,d⟩ <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem box_first (b : Rect) (x y direction range : Nat) (h : b.Valid) :
    FirstHit (BoxHit b x y direction) range (boxDistance b x y direction range) := by
  unfold BoxHit boxDistance
  rcases h with ⟨hx,_,hy,_⟩
  split
  · exact axis_first _ _ _ _ _ _ _ hx
  · split
    · apply axis_first; omega
    · split
      · exact axis_first _ _ _ _ _ _ _ hy
      · apply axis_first; omega

theorem trace_first (boxes : List Rect) (x y direction range : Nat)
    (valid : ∀ b ∈ boxes, b.Valid) :
    FirstHit (fun t => ∃ b ∈ boxes, BoxHit b x y direction t) range
      (trace boxes x y direction range) := by
  induction boxes with
  | nil => simp [trace, FirstHit]
  | cons b rest ih =>
    have hb := box_first b x y direction range (valid b (by simp))
    have hr := ih (fun c hc => valid c (by simp [hc]))
    simpa [trace, List.mem_cons, or_and_right, exists_or, exists_eq_left] using first_min hb hr

#print axioms trace_first
end Project.Lidar.Continuous
