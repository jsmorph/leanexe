import LeanExe.WGSL.LidarSummary
import Lean.Elab.Tactic.Omega

namespace Project.Lidar.Summary
open LeanExe.WGSL

def requested (mask i : Nat) : Bool := mask / 2^i % 2 == 1

private theorem finite_masks : ∀ i : Fin 4, ∀ mask : Fin 16,
    (LidarSummary.selected i).eval ⟨fun _ => 0, fun _ => mask, 0⟩ =
      if requested mask i then 1 else 0 := by decide +kernel

theorem selected (input : UInt.Input) (i : Nat) (hi : i < 4) (hm : input.params 3 < 16) :
    (LidarSummary.selected i).eval input = if requested (input.params 3) i then 1 else 0 := by
  have same : (LidarSummary.selected i).eval input =
      (LidarSummary.selected i).eval ⟨fun _ => 0, fun _ => input.params 3, 0⟩ := by
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl <;> rfl
  rw [same]
  exact finite_masks ⟨i,hi⟩ ⟨input.params 3,hm⟩

def hits (input : UInt.Input) (i : Nat) : Nat :=
  if requested (input.params 3) i && decide (input.scene i ≤ input.params 2) then 1 else 0

def distance (input : UInt.Input) (i : Nat) : Nat :=
  if requested (input.params 3) i then input.scene i else input.params 2+1

def count (input : UInt.Input) : Nat := hits input 0 + hits input 1 + hits input 2 + hits input 3

def nearest (input : UInt.Input) : Nat := min (distance input 0)
  (min (distance input 1) (min (distance input 2) (distance input 3)))

theorem count_one (input : UInt.Input) (i : Nat) (hi : i < 4) (hm : input.params 3 < 16) :
    (LidarSummary.count i).eval input = hits input i * 8192 := by
  simp only [LidarSummary.count, UInt.Expr.eval, selected input i hi hm]
  unfold hits
  cases requested (input.params 3) i <;> by_cases h : input.scene i ≤ input.params 2 <;> simp [h]

theorem distance_one (input : UInt.Input) (i : Nat) (hi : i < 4) (hm : input.params 3 < 16) :
    (LidarSummary.distance i).eval input = distance input i := by
  simp only [LidarSummary.distance, LidarSummary.miss, UInt.Expr.eval, selected input i hi hm]
  unfold distance
  cases requested (input.params 3) i <;> rfl

theorem correct (input : UInt.Input) (bounded : input.Bounded 4096) (hm : input.params 3 < 16) :
    LidarSummary.kernel.eval32 input = count input * 8192 + nearest input := by
  rw [LidarSummary.exact input bounded]
  simp only [LidarSummary.kernel, UInt.Expr.eval,
    count_one input 0 (by decide) hm, count_one input 1 (by decide) hm,
    count_one input 2 (by decide) hm, count_one input 3 (by decide) hm,
    distance_one input 0 (by decide) hm, distance_one input 1 (by decide) hm,
    distance_one input 2 (by decide) hm, distance_one input 3 (by decide) hm]
  unfold count nearest
  simp only [Nat.add_mul, Nat.add_assoc]

theorem decode (input : UInt.Input) (h : nearest input < 8192) :
    (count input*8192 + nearest input) / 8192 = count input ∧
    (count input*8192 + nearest input) % 8192 = nearest input := by omega

#print axioms correct
end Project.Lidar.Summary
