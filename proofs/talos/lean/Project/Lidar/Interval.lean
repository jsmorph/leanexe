import Project.Lidar.Oblique
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

namespace Project.Lidar.Interval
open LeanExe.Examples.Lidar

structure RealRect where
  x0 : ℝ
  y0 : ℝ
  x1 : ℝ
  y1 : ℝ

def ofRect (b : Rect) : RealRect := ⟨b.x0, b.y0, b.x1, b.y1⟩

/-- Inclusion of closed rectangles, stated on their endpoint bounds. -/
def Enclosed (small large : RealRect) : Prop :=
  large.x0 ≤ small.x0 ∧ small.x1 ≤ large.x1 ∧
    large.y0 ≤ small.y0 ∧ small.y1 ≤ large.y1

def BoxHit (b : RealRect) (x y direction : Nat) (t : ℝ) : Prop :=
  b.x0 ≤ x + Oblique.velocityX direction*t ∧
    (x : ℝ)+Oblique.velocityX direction*t ≤ b.x1 ∧
    b.y0 ≤ y + Oblique.velocityY direction*t ∧
    (y : ℝ)+Oblique.velocityY direction*t ≤ b.y1

theorem ofRect_hit (b : Rect) (x y direction : Nat) (t : ℝ) :
    BoxHit (ofRect b) x y direction t ↔ Oblique.GeometricHit b x y direction t := Iff.rfl

theorem hit_mono {small large : RealRect} (h : Enclosed small large)
    {x y direction : Nat} {t : ℝ} (hit : BoxHit small x y direction t) :
    BoxHit large x y direction t :=
  ⟨le_trans h.1 hit.1, le_trans hit.2.1 h.2.1,
    le_trans h.2.2.1 hit.2.2.1, le_trans hit.2.2.2 h.2.2.2⟩

theorem closed_box (b : RealRect) (x y direction : Nat) :
    IsClosed {t | BoxHit b x y direction t} := by
  have px : Continuous (fun t : ℝ => (x : ℝ)+Oblique.velocityX direction*t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have py : Continuous (fun t : ℝ => (y : ℝ)+Oblique.velocityY direction*t) :=
    continuous_const.add (continuous_const.mul continuous_id)
  exact (isClosed_le continuous_const px).inter
    ((isClosed_le px continuous_const).inter
      ((isClosed_le continuous_const py).inter (isClosed_le py continuous_const)))

def Hits (boxes : List RealRect) (x y direction : Nat) (t : ℝ) : Prop :=
  ∃ b ∈ boxes, BoxHit b x y direction t

theorem closed_hits (boxes : List RealRect) (x y direction : Nat) :
    IsClosed {t | Hits boxes x y direction t} := by
  induction boxes with
  | nil => simpa [Hits] using (isClosed_empty : IsClosed (∅ : Set ℝ))
  | cons b rest ih =>
    convert (closed_box b x y direction).union ih using 1
    ext t
    simp [Hits, or_and_right, exists_or, exists_eq_left]

/-- Exact nearest-hit contract in physical distance units. -/
def First (hit : ℝ → Prop) (range : Nat) (distance : ℝ) : Prop :=
  0 ≤ distance ∧ distance ≤ (range : ℝ)/60 ∧ hit distance ∧
    ∀ t, 0 ≤ t → t ≤ (range : ℝ)/60 → hit t → distance ≤ t

theorem nearest_exists (hit : ℝ → Prop) (range : Nat)
    (closed : IsClosed {t | hit t})
    (witness : ∃ t, 0 ≤ t ∧ t ≤ (range : ℝ)/60 ∧ hit t) :
    ∃ distance, First hit range distance := by
  let times := Set.Icc 0 ((range : ℝ)/60) ∩ {t | hit t}
  have compact : IsCompact times := isCompact_Icc.inter_right closed
  obtain ⟨t,ht0,htr,hit⟩ := witness
  obtain ⟨distance,least⟩ := compact.exists_isLeast ⟨t,⟨ht0,htr⟩,hit⟩
  exact ⟨distance,least.1.1.1,least.1.1.2,least.1.2,
    fun _ h0 hr hh => least.2 ⟨⟨h0,hr⟩,hh⟩⟩

/-- If even the outer approximation misses, the actual scene misses. -/
theorem certified_miss (actual outer : ℝ → Prop) (range lower : Nat)
    (outside : ∀ t, actual t → outer t)
    (first : Continuous.FirstHit (fun ticks => outer (ticks/60)) range lower)
    (miss : range < lower) :
    ∀ t, 0 ≤ t → t ≤ (range : ℝ)/60 → ¬actual t := by
  intro t ht hr hit
  have scale : 60*t/60 = t := by ring
  have bound := first.2.2 (60*t) (by linarith) (by linarith)
    (by simpa only [scale] using outside t hit)
  have hm : (range : ℝ) < lower := by exact_mod_cast miss
  linarith

/-- An inner hit gives a real hit; the outer and inner answers bound its
nearest distance. The midpoint error bound is expressed in physical units. -/
theorem certified_hit (actual inner outer : ℝ → Prop) (range lower upper : Nat)
    (closed : IsClosed {t | actual t})
    (inside : ∀ t, inner t → actual t) (outside : ∀ t, actual t → outer t)
    (lo : Continuous.FirstHit (fun ticks => outer (ticks/60)) range lower)
    (hi : Continuous.FirstHit (fun ticks => inner (ticks/60)) range upper)
    (hit : upper ≤ range) :
    ∃ distance, First actual range distance ∧
      (lower : ℝ)/60 ≤ distance ∧ distance ≤ (upper : ℝ)/60 ∧
      |((lower : ℝ)+upper)/120-distance| ≤ ((upper : ℝ)-lower)/120 := by
  have hu0 : (0 : ℝ) ≤ (upper : ℝ)/60 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
  have hur : (upper : ℝ)/60 ≤ (range : ℝ)/60 :=
    div_le_div_of_nonneg_right (by exact_mod_cast hit) (by norm_num)
  have witness := inside ((upper : ℝ)/60) (hi.2.1 hit)
  obtain ⟨distance,first⟩ := nearest_exists actual range closed ⟨_,hu0,hur,witness⟩
  have upperBound := first.2.2.2 _ hu0 hur witness
  have scale : 60*distance/60 = distance := by ring
  have lowerBound := lo.2.2 (60*distance) (by linarith [first.1]) (by linarith [first.2.1])
    (by simpa only [scale] using outside distance first.2.2.1)
  refine ⟨distance,first,by linarith,upperBound,?_⟩
  rw [abs_le]
  constructor <;> linarith

#print axioms certified_miss
#print axioms certified_hit
end Project.Lidar.Interval
