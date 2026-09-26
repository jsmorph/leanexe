import LeanExe.WGSL.LidarInterval
import LeanExe.WGSL.LidarSummary

namespace LeanExe.WGSL.UInt

/-- Check which parameter prefix a shader can observe. -/
def Expr.readsBelow (n : Nat) : Expr → Bool
  | .lit _ | .direction | .read .scene _ => true
  | .read .params i => decide (i < n)
  | .add a b | .mul a b | .sub a b | .min a b | .le a b | .eq a b | .both a b =>
      a.readsBelow n && b.readsBelow n
  | .choose c a b => c.readsBelow n && a.readsBelow n && b.readsBelow n

/-- Changing unobserved parameter words preserves the modeled u32 result,
including its wrapping behavior. No bounded-arithmetic assumption is needed. -/
theorem eval32_stable (e : Expr) (n : Nat) (checked : e.readsBelow n = true)
    (a b : Input) (scene : a.scene = b.scene) (direction : a.direction = b.direction)
    (params : ∀ i, i < n → a.params i = b.params i) : e.eval32 a = e.eval32 b := by
  induction e with
  | lit => rfl
  | direction => simp only [Expr.eval32, direction]
  | read buffer i =>
    cases buffer
    · simp only [Expr.eval32, scene]
    · have hi : i < n := by simpa [Expr.readsBelow] using checked
      simp only [Expr.eval32, params i hi]
  | add x y hx hy | mul x y hx hy | sub x y hx hy | min x y hx hy | le x y hx hy | eq x y hx hy | both x y hx hy =>
    have h : x.readsBelow n = true ∧ y.readsBelow n = true := by
      simpa only [Expr.readsBelow, Bool.and_eq_true] using checked
    simp only [Expr.eval32, hx h.1, hy h.2]
  | choose c x y hc hx hy =>
    have h : (c.readsBelow n = true ∧ x.readsBelow n = true) ∧ y.readsBelow n = true := by
      simpa only [Expr.readsBelow, Bool.and_eq_true] using checked
    simp only [Expr.eval32, hc h.1.1, hx h.1.2, hy h.2]

theorem cardinal_scan_prefix : Lidar.kernel.readsBelow 3 = true := by decide
theorem oblique_scan_prefix : LidarOblique.kernel.readsBelow 3 = true := by decide
theorem inner_scan_prefix : LidarInterval.inner.readsBelow 3 = true := by decide
theorem outer_scan_prefix : LidarInterval.outer.readsBelow 3 = true := by decide

theorem summary_uses_mask : LidarSummary.kernel.readsBelow 3 = false := by decide

#print axioms eval32_stable
end LeanExe.WGSL.UInt
