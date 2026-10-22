import Library.Numerics.Float64.Atan.AtanTheoremPoly
import LeanExe.ProofKit.F64UpperWord

/-!
The branches of `Atan.atan` as equations.  `ixOf x` is the high word of `|x|`.  From `2 ^ 66` on the
result is `±(atanhi3 + atanlo3)`, below `2 ^ -27` it is `x` itself, below `0.4375` it is
`x - x * atanS x`, and otherwise it is `±atanTail hi lo t` with the reduced argument `t` and the
constants `hi`, `lo` of its interval, negated for a negative `x`.
-/

namespace Library.Numerics.Float64.Atan.AtanTheoremBranches
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx AtanTheoremPoly

set_option exponentiation.threshold 4096

/-- The high word of `|x|`. -/
def ixOf (x : Float) : UInt64 := (x.toBits >>> 32) &&& 0x7fffffff

/-- The end of `Atan.atan` for the reduced argument `t` and the constants `hi`, `lo`. -/
def atanTail (hi lo t : Float) : Float := hi - ((t * atanS t - lo) - t)

theorem atan_poly_eq (x : Float) (h1 : ¬ ixOf x ≥ 0x44100000) (h2 : ¬ ixOf x < 0x3e400000)
    (h3 : ixOf x < 0x3fdc0000) : Atan.atan x = x - x * atanS x := by
  unfold ixOf at h1 h2 h3
  simp only [Atan.atan, h1, h2, h3, ite_false, ite_true, decide_false, Bool.false_and,
    Bool.false_eq_true]
  rfl

theorem atan_tiny_eq (x : Float) (h1 : ixOf x < 0x3e400000)
    (hh : Float.ofBits 0x7E37E43C8800759C + x > 1.0) : Atan.atan x = x := by
  have h0 : ¬ ixOf x ≥ 0x44100000 := by
    intro h
    have a := UInt64.lt_iff_toNat_lt.mp h1
    have b := UInt64.le_iff_toNat_le.mp h
    simp at a b
    omega
  unfold ixOf at h0 h1
  simp only [Atan.atan, h0, h1, hh, ite_false, ite_true, decide_true, Bool.and_true]

theorem atan_tail0_eq (x : Float) (h1 : ¬ ixOf x ≥ 0x44100000) (h3 : ¬ ixOf x < 0x3fdc0000)
    (h4 : ixOf x < 0x3ff30000) (h5 : ixOf x < 0x3fe60000) :
    Atan.atan x =
      let z := atanTail (Float.ofBits 0x3FDDAC670561BB4F) (Float.ofBits 0x3C7A2B7F222F65E2)
        ((2.0 * x.abs - 1.0) / (2.0 + x.abs))
      if x.toBits >>> 32 >>> 31 == 1 then -z else z := by
  have h2 : ¬ ixOf x < 0x3e400000 := by
    intro h
    apply h3
    have a := UInt64.lt_iff_toNat_lt.mp h
    apply UInt64.lt_iff_toNat_lt.mpr
    simp at a ⊢
    omega
  unfold ixOf at h1 h2 h3 h4 h5
  simp only [Atan.atan, h1, h2, h3, h4, h5, ite_false, ite_true, decide_false, Bool.false_and,
    Bool.false_eq_true]
  rfl

theorem high_chain (x : Float) (h3 : ¬ ixOf x < 0x3fdc0000) : ¬ ixOf x < 0x3e400000 := by
  intro h
  apply h3
  have a := UInt64.lt_iff_toNat_lt.mp h
  apply UInt64.lt_iff_toNat_lt.mpr
  simp at a ⊢
  omega

theorem atan_tail1_eq (x : Float) (h1 : ¬ ixOf x ≥ 0x44100000) (h3 : ¬ ixOf x < 0x3fdc0000)
    (h4 : ixOf x < 0x3ff30000) (h5 : ¬ ixOf x < 0x3fe60000) :
    Atan.atan x =
      let z := atanTail (Float.ofBits 0x3FE921FB54442D18) (Float.ofBits 0x3C81A62633145C07)
        ((x.abs - 1.0) / (x.abs + 1.0))
      if x.toBits >>> 32 >>> 31 == 1 then -z else z := by
  have h2 := high_chain x h3
  unfold ixOf at h1 h2 h3 h4 h5
  simp only [Atan.atan, h1, h2, h3, h4, h5, ite_false, ite_true, decide_false, Bool.false_and,
    Bool.false_eq_true]
  rfl

theorem atan_tail2_eq (x : Float) (h1 : ¬ ixOf x ≥ 0x44100000) (h3 : ¬ ixOf x < 0x3fdc0000)
    (h4 : ¬ ixOf x < 0x3ff30000) (h6 : ixOf x < 0x40038000) :
    Atan.atan x =
      let z := atanTail (Float.ofBits 0x3FEF730BD281F69B) (Float.ofBits 0x3C7007887AF0CBBD)
        ((x.abs - 1.5) / (1.0 + 1.5 * x.abs))
      if x.toBits >>> 32 >>> 31 == 1 then -z else z := by
  have h2 := high_chain x h3
  unfold ixOf at h1 h2 h3 h4 h6
  simp only [Atan.atan, h1, h2, h3, h4, h6, ite_false, ite_true, decide_false, Bool.false_and,
    Bool.false_eq_true]
  rfl

theorem atan_tail3_eq (x : Float) (h1 : ¬ ixOf x ≥ 0x44100000) (h3 : ¬ ixOf x < 0x3fdc0000)
    (h4 : ¬ ixOf x < 0x3ff30000) (h6 : ¬ ixOf x < 0x40038000) :
    Atan.atan x =
      let z := atanTail (Float.ofBits 0x3FF921FB54442D18) (Float.ofBits 0x3C91A62633145C07)
        (-1.0 / x.abs)
      if x.toBits >>> 32 >>> 31 == 1 then -z else z := by
  have h2 := high_chain x h3
  unfold ixOf at h1 h2 h3 h4 h6
  simp only [Atan.atan, h1, h2, h3, h4, h6, ite_false, ite_true, decide_false, Bool.false_and,
    Bool.false_eq_true]
  rfl

#print axioms atan_poly_eq
#print axioms atan_tiny_eq
#print axioms atan_tail0_eq
#print axioms atan_tail1_eq
#print axioms atan_tail2_eq
#print axioms atan_tail3_eq

end Library.Numerics.Float64.Atan.AtanTheoremBranches
