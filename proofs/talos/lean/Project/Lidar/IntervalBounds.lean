import Project.Lidar.Interval
import LeanExe.Examples.LidarInterval

namespace Project.Lidar.Interval
open LeanExe.Examples.Lidar

/-- Input quantization uncertainty, rather than a random sensor-noise model. -/
def Approx (nominal : Rect) (actual : RealRect) : Prop :=
  |actual.x0-nominal.x0| ≤ 1 ∧ |actual.x1-nominal.x1| ≤ 1 ∧
    |actual.y0-nominal.y0| ≤ 1 ∧ |actual.y1-nominal.y1| ≤ 1

theorem enclosure (nominal : Rect) (actual : RealRect)
    (domain : LeanExe.Examples.LidarInterval.Domain nominal) (approx : Approx nominal actual) :
    Enclosed (ofRect (LeanExe.Examples.LidarInterval.inner nominal)) actual ∧
      Enclosed actual (ofRect (LeanExe.Examples.LidarInterval.outer nominal)) := by
  rcases domain with ⟨hx0,hx,hx1,hy0,hy,hy1⟩
  have hx1' : 1 ≤ nominal.x1 := by omega
  have hy1' : 1 ≤ nominal.y1 := by omega
  rcases approx with ⟨a,b,c,d⟩
  rw [abs_le] at a b c d
  simp only [Enclosed, ofRect, LeanExe.Examples.LidarInterval.inner,
    LeanExe.Examples.LidarInterval.outer, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub hx0, Nat.cast_sub hy0, Nat.cast_sub hx1', Nat.cast_sub hy1']
  constructor <;> refine ⟨?_,?_,?_,?_⟩ <;> linarith

theorem hits_mono {small large : List RealRect} (enclosed : List.Forall₂ Enclosed small large)
    (x y direction : Nat) : ∀ t, Hits small x y direction t → Hits large x y direction t := by
  induction enclosed with
  | nil => simp [Hits]
  | @cons a b as bs ab rest ih =>
    intro t hit
    obtain ⟨c,hc,hit⟩ := hit
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨b,by simp,hit_mono ab hit⟩
    · obtain ⟨d,hd,hit⟩ := ih t ⟨c,hc,hit⟩
      exact ⟨d,by simp [hd],hit⟩

theorem scene_enclosure {nominal : List Rect} {actual : List RealRect}
    (domain : ∀ b ∈ nominal, LeanExe.Examples.LidarInterval.Domain b)
    (approx : List.Forall₂ Approx nominal actual) :
    List.Forall₂ Enclosed (nominal.map (ofRect ∘ LeanExe.Examples.LidarInterval.inner)) actual ∧
      List.Forall₂ Enclosed actual (nominal.map (ofRect ∘ LeanExe.Examples.LidarInterval.outer)) := by
  induction approx with
  | nil => exact ⟨.nil,.nil⟩
  | @cons a b as bs ab rest ih =>
    have h := enclosure a b (domain a (by simp)) ab
    have tail := ih (fun c hc => domain c (by simp [hc]))
    exact ⟨.cons h.1 tail.1, .cons h.2 tail.2⟩

#print axioms scene_enclosure
end Project.Lidar.Interval
