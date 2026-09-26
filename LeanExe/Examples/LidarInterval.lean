import LeanExe.Examples.Lidar

namespace LeanExe.Examples.LidarInterval
open LeanExe.Examples.Lidar

/-- The nominal box leaves room for one-unit outward expansion and inward
contraction. The contracted rectangle may be degenerate but remains closed. -/
def Domain (b : Rect) : Prop :=
  1 ≤ b.x0 ∧ b.x0+2 ≤ b.x1 ∧ b.x1 ≤ 4094 ∧
    1 ≤ b.y0 ∧ b.y0+2 ≤ b.y1 ∧ b.y1 ≤ 4094

instance (b : Rect) : Decidable (Domain b) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def inner (b : Rect) : Rect := ⟨b.x0+1,b.y0+1,b.x1-1,b.y1-1⟩
def outer (b : Rect) : Rect := ⟨b.x0-1,b.y0-1,b.x1+1,b.y1+1⟩

theorem inner_valid (b : Rect) (h : Domain b) : (inner b).Valid := by
  rcases h with ⟨_,_,_,_,_,_⟩
  simp only [inner, Rect.Valid, world]
  omega

theorem outer_valid (b : Rect) (h : Domain b) : (outer b).Valid := by
  rcases h with ⟨_,_,_,_,_,_⟩
  simp only [outer, Rect.Valid, world]
  omega

end LeanExe.Examples.LidarInterval
