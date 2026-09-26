import LeanExe.Examples.Lidar
import Lean.Elab.Tactic.Omega

namespace Project.Lidar
open LeanExe.Examples.Lidar

/-- Independent geometric membership for a positive-axis ray at integer time. -/
def AxisHit (lo hi low high origin transverse t : Nat) : Prop :=
  low ≤ transverse ∧ transverse ≤ high ∧ lo ≤ origin+t ∧ origin+t ≤ hi

/-- A hit is attained, is minimal among all in-range intersections, or is
the unique miss sentinel. This specification is independent of the algorithm. -/
def FirstHit (hit : Nat → Prop) (range answer : Nat) : Prop :=
  answer ≤ range+1 ∧ (answer ≤ range → hit answer) ∧
  ∀ t, t ≤ range → hit t → answer ≤ t

theorem axis_first (lo hi low high origin transverse range : Nat) (ordered : lo ≤ hi) :
    FirstHit (AxisHit lo hi low high origin transverse) range
      (axisDistance lo hi low high origin transverse range) := by
  unfold axisDistance
  split
  · rename_i h
    split
    · rename_i hr
      unfold FirstHit AxisHit
      exact ⟨by omega, by intro; omega, by intros; omega⟩
    · rename_i hr
      unfold FirstHit AxisHit
      exact ⟨by omega, by omega, by intros; omega⟩
  · rename_i h
    unfold FirstHit AxisHit
    exact ⟨by omega, by omega, by intros; omega⟩

theorem first_min {a b : Nat → Prop} {range da db : Nat}
    (ha : FirstHit a range da) (hb : FirstHit b range db) :
    FirstHit (fun t => a t ∨ b t) range (min da db) := by
  rcases ha with ⟨ha0, ha1, ha2⟩
  rcases hb with ⟨hb0, hb1, hb2⟩
  by_cases h : da ≤ db
  · rw [Nat.min_eq_left h]
    exact ⟨ha0, fun hd => Or.inl (ha1 hd), fun t ht hit =>
      hit.elim (ha2 t ht) (fun hbt => Nat.le_trans h (hb2 t ht hbt))⟩
  · have h' : db ≤ da := by omega
    rw [Nat.min_eq_right h']
    exact ⟨hb0, fun hd => Or.inr (hb1 hd), fun t ht hit =>
      hit.elim (fun hat => Nat.le_trans h' (ha2 t ht hat)) (hb2 t ht)⟩

theorem miss_iff {hit range answer} (h : FirstHit hit range answer) :
    answer = range+1 ↔ ∀ t, t ≤ range → ¬hit t := by
  rcases h with ⟨h0,h1,h2⟩
  constructor
  · intro he t ht hh
    have := h2 t ht hh
    omega
  · intro hn
    by_cases ha : answer ≤ range
    · exact False.elim (hn answer ha (h1 ha))
    · omega

/-- Membership after rotating/reflection into positive-axis coordinates. -/
def BoxHit (b : Rect) (x y direction t : Nat) : Prop :=
  if direction = 0 then AxisHit b.x0 b.x1 b.y0 b.y1 x y t
  else if direction = 1 then AxisHit (world-b.x1) (world-b.x0) b.y0 b.y1 (world-x) y t
  else if direction = 2 then AxisHit b.y0 b.y1 b.x0 b.x1 y x t
  else AxisHit (world-b.y1) (world-b.y0) b.x0 b.x1 (world-y) x t

theorem box_first (b : Rect) (x y direction range : Nat) (h : b.Valid) :
    FirstHit (BoxHit b x y direction) range (boxDistance b x y direction range) := by
  unfold BoxHit boxDistance
  rcases h with ⟨hx, _, hy, _⟩
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

#print axioms axis_first
#print axioms trace_first
#print axioms miss_iff
end Project.Lidar
