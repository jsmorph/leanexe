import LeanExe.Examples.Lidar
import Lean.Elab.Tactic.Omega

namespace Project.Lidar.Controller
open LeanExe.Examples.Lidar

theorem packed (x y range mask : UInt64)
    (hx : x ≤ 4095) (hy : y ≤ 4095) (hr : range ≤ 4095) (hm : mask ≤ 15) :
    parameters x y range mask = x + y*4096 + range*16777216 + mask*68719476736 := by
  simp [parameters, hx, hy, hr, hm]

theorem rejected (x y range mask : UInt64)
    (h : ¬ (x ≤ 4095 ∧ y ≤ 4095 ∧ range ≤ 4095 ∧ mask ≤ 15)) :
    parameters x y range mask = 18446744073709551615 := by
  simp [parameters, h]

theorem packed_nat (x y range mask : UInt64)
    (hx : x ≤ 4095) (hy : y ≤ 4095) (hr : range ≤ 4095) (hm : mask ≤ 15) :
    (parameters x y range mask).toNat =
      x.toNat + y.toNat*4096 + range.toNat*16777216 + mask.toNat*68719476736 := by
  rw [packed x y range mask hx hy hr hm]
  change x.toNat ≤ 4095 at hx
  change y.toNat ≤ 4095 at hy
  change range.toNat ≤ 4095 at hr
  change mask.toNat ≤ 15 at hm
  simp only [UInt64.toNat_add, UInt64.toNat_mul]
  have c1 : (4096 : UInt64).toNat = 4096 := rfl
  have c2 : (16777216 : UInt64).toNat = 16777216 := rfl
  have c3 : (68719476736 : UInt64).toNat = 68719476736 := rfl
  rw [c1, c2, c3]
  omega

/-- The host's four field extractions from the packed mathematical word.
All arithmetic is integral and fits well within the controller's 64-bit word. -/
theorem fields (x y range mask : Nat) (hx : x < 4096) (hy : y < 4096)
    (hr : range < 4096) (hm : mask < 16) :
    let packed := x + y*4096 + range*16777216 + mask*68719476736
    packed < 1099511627776 ∧
    packed % 4096 = x ∧ packed / 4096 % 4096 = y ∧
    packed / 16777216 % 4096 = range ∧ packed / 68719476736 % 16 = mask := by
  dsimp
  omega

#print axioms fields
end Project.Lidar.Controller
