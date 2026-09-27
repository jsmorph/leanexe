import Project.ExpArm.Model
import Init.Omega

namespace Project.ExpArm

theorem exp_tiny (x : UInt64)
    (h : x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000) :
    exp x = 0x3FF0000000000000 := by
  simp [exp, h]

theorem exp_nan (x : UInt64)
    (h : 0x7FF0000000000000 < x &&& 0x7FFFFFFFFFFFFFFF) :
    exp x = 0x7FF8000000000000 := by
  have hs : ¬x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000 := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  have hb : 0x4090000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  simp [exp, hs, hb, h]

theorem exp_large (x : UInt64)
    (hl : 0x4090000000000000 ≤ x &&& 0x7FFFFFFFFFFFFFFF)
    (hu : x &&& 0x7FFFFFFFFFFFFFFF ≤ 0x7FF0000000000000) :
    exp x = if x >>> 63 = 0 then 0x7FF0000000000000 else 0 := by
  have hs : ¬x &&& 0x7FFFFFFFFFFFFFFF < 0x3C90000000000000 := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  have hn : ¬0x7FF0000000000000 < x &&& 0x7FFFFFFFFFFFFFFF := by
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at *
    omega
  simp [exp, hs, hl, hn]

theorem exp_zeros : exp 0 = 0x3FF0000000000000 ∧
    exp 0x8000000000000000 = 0x3FF0000000000000 := by
  constructor <;> apply exp_tiny <;> decide

theorem exp_infinities : exp 0x7FF0000000000000 = 0x7FF0000000000000 ∧
    exp 0xFFF0000000000000 = 0 := by
  constructor
  · exact exp_large _ (by decide) (by decide)
  · exact exp_large _ (by decide) (by decide)

end Project.ExpArm
