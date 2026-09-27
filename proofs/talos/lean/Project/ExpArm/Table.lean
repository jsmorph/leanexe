import Project.ExpArm.Model
import Init.Omega

namespace Project.ExpArm

set_option maxRecDepth 4096

theorem table_size : table.size = 256 := rfl

theorem index_bound (k : UInt64) : (2 * (k &&& 127)).toNat ≤ 254 := by
  have h : (k &&& 127).toNat ≤ 127 :=
    UInt64.le_iff_toNat_le.mp UInt64.and_le_right
  rw [UInt64.toNat_mul]
  change (2 * (k &&& 127).toNat) % 18446744073709551616 ≤ 254
  omega

theorem index_next (k : UInt64) :
    (2 * (k &&& 127) + 1).toNat = (2 * (k &&& 127)).toNat + 1 := by
  have h := index_bound k
  rw [UInt64.toNat_add]
  change ((2 * (k &&& 127)).toNat + 1) % 18446744073709551616 = _
  omega

end Project.ExpArm
