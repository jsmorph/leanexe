import LeanExe.ProofKit.F64Order

namespace LeanExe.ProofKit.F64ExponentBounds
open CodeLib.IEEE64 F64Order

set_option exponentiation.threshold 4096

def boundary (e : Nat) : UInt64 := UInt64.ofNat (e * 2 ^ 52)

theorem boundary_fields (e : Nat) (he : e < 2048) :
    (boundary e).toNat = e * 2 ^ 52 ∧ absBits (boundary e) = boundary e := by
  have hn : e * 2 ^ 52 < 2 ^ 63 := by
    calc
      _ < 2048 * 2 ^ 52 := Nat.mul_lt_mul_of_pos_right he (Nat.two_pow_pos 52)
      _ = _ := by norm_num
  have hw : (boundary e).toNat = e * 2 ^ 52 :=
    UInt64.toNat_ofNat_of_lt' (hn.trans (by norm_num : 2 ^ 63 < 2 ^ 64))
  refine ⟨hw, ?_⟩
  apply UInt64.toNat_inj.mp
  rw [absBits_toNat, hw, Nat.mod_eq_of_lt hn]

theorem magnitude_le_boundary (x : UInt64) (e : Nat) (he : e < 2048)
    (hx : Wasm.IEEE64.exponent x < e) :
    |value x| ≤ |value (boundary e)| := by
  have hb := boundary_fields e he
  apply abs_value_mono x (boundary e)
  rw [hb.2]
  apply UInt64.le_iff_toNat_le.mpr
  rw [hb.1]
  rw [exponent_abs] at hx
  omega

theorem exponent_lt_of_magnitude_lt (x : UInt64) (e : Nat) (he : e < 2048)
    (hx : |value x| < |value (boundary e)|) :
    Wasm.IEEE64.exponent x < e := by
  by_contra hn
  have hb := boundary_fields e he
  have hord : absBits (boundary e) ≤ absBits x := by
    rw [hb.2]
    apply UInt64.le_iff_toNat_le.mpr
    rw [hb.1]
    rw [exponent_abs] at hn
    omega
  exact (not_lt_of_ge (abs_value_mono (boundary e) x hord)) hx

#print axioms boundary_fields
#print axioms magnitude_le_boundary
#print axioms exponent_lt_of_magnitude_lt

end LeanExe.ProofKit.F64ExponentBounds
