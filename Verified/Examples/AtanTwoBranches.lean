import Verified.Examples.AtanTheoremSpecial

/-!
The branches of `Atan.atan2 y x` as equations.  `quadTail z m` is the code's last step for the
angle `z` of `|y/x|` and the quadrant `m`, whose bit 0 is the sign of `y` and whose bit 1 is the
sign of `x`.  `kOf2` is the shifted difference of the high words, which is the difference of the
exponents or one less.
-/

namespace Verified.Examples.AtanTwoBranches
open CodeLib.IEEE64 LeanExe.ProofKit AtanTheoremBranches

set_option exponentiation.threshold 4096

def lxOf (x : Float) : UInt64 := x.toBits &&& 0xFFFFFFFF

def piF : Float := Float.ofBits 0x400921FB54442D18

def piLoF : Float := Float.ofBits 0x3CA1A62633145C07

def quadTail (z : Float) (m : UInt64) : Float :=
  if m == 0 then z else if m == 1 then -z else if m == 2 then piF - (z - piLoF)
  else (z - piLoF) - piF

def mOf (y x : Float) : UInt64 :=
  ((y.toBits >>> 32 >>> 31) &&& (1 : UInt64)) ||| ((x.toBits >>> 32 >>> 30) &&& (2 : UInt64))

def kOf2 (y x : Float) : UInt64 :=
  (ixOf y - ixOf x) >>> 20 |||
    (if (ixOf y - ixOf x) >>> 63 == 1 then 0xFFFFF00000000000 else 0)

/-- Neither input is NaN. -/
def notNaN (y x : Float) : Prop :=
  ((ixOf x ||| ((lxOf x ||| ((0 - lxOf x) &&& 0xFFFFFFFF)) >>> 31)) > 0x7ff00000 ||
    (ixOf y ||| ((lxOf y ||| ((0 - lxOf y) &&& 0xFFFFFFFF)) >>> 31)) > 0x7ff00000) = false

/-- The general branch: finite nonzero inputs, `x ≠ 1`, and `|y/x|` between the shortcuts. -/
theorem atan2_gen_eq (y x : Float) (hn : notNaN y x)
    (h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false)
    (h2 : (ixOf y ||| lxOf y == 0) = false) (h3 : (ixOf x ||| lxOf x == 0) = false)
    (h4 : (ixOf x == 0x7ff00000) = false) (h5 : (ixOf y == 0x7ff00000) = false)
    (h6 : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = false)
    (h7 : (x.toBits >>> 32 >>> 31 == 1 && kOf2 y x >>> 63 == 1 &&
      decide (kOf2 y x < 0xFFFFFFFFFFFFFFC4)) = false) :
    Atan.atan2 y x = quadTail (Atan.atan (y / x).abs) (mOf y x) := by
  unfold notNaN kOf2 mOf ixOf lxOf at *
  simp only [Atan.atan2, hn, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ite_false]
  rfl

/-- `|y/x|` above `2 ^ 60`: the result is `±(pio2_hi + pio2_lo/2)`. -/
theorem atan2_big_eq (y x : Float) (hn : notNaN y x)
    (h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false)
    (h2 : (ixOf y ||| lxOf y == 0) = false) (h3 : (ixOf x ||| lxOf x == 0) = false)
    (h4 : (ixOf x == 0x7ff00000) = false) (h5 : (ixOf y == 0x7ff00000) = false)
    (h6 : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = true) :
    Atan.atan2 y x = quadTail (Float.ofBits 0x3FF921FB54442D18 + 0.5 * piLoF)
      (mOf y x &&& (1 : UInt64)) := by
  unfold notNaN kOf2 mOf ixOf lxOf at *
  simp only [Atan.atan2, hn, h1, h2, h3, h4, h5, h6, Bool.false_eq_true, ite_false, ite_true]
  rfl

/-- Negative `x` and `|y/x|` below `2 ^ -60`: the angle is taken as 0. -/
theorem atan2_tiny_eq (y x : Float) (hn : notNaN y x)
    (h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false)
    (h2 : (ixOf y ||| lxOf y == 0) = false) (h3 : (ixOf x ||| lxOf x == 0) = false)
    (h4 : (ixOf x == 0x7ff00000) = false) (h5 : (ixOf y == 0x7ff00000) = false)
    (h6 : (kOf2 y x >>> 63 == 0 && decide (kOf2 y x > 60)) = false)
    (h7 : (x.toBits >>> 32 >>> 31 == 1 && kOf2 y x >>> 63 == 1 &&
      decide (kOf2 y x < 0xFFFFFFFFFFFFFFC4)) = true) :
    Atan.atan2 y x = quadTail 0.0 (mOf y x) := by
  unfold notNaN kOf2 mOf ixOf lxOf at *
  simp only [Atan.atan2, hn, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true, ite_false,
    ite_true]
  rfl

/-- `x = ±0` and `y ≠ 0`: the result is `±(pio2_hi + tiny)` by the sign of `y`. -/
theorem atan2_xzero_eq (y x : Float) (hn : notNaN y x)
    (h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = false)
    (h2 : (ixOf y ||| lxOf y == 0) = false) (h3 : (ixOf x ||| lxOf x == 0) = true) :
    Atan.atan2 y x = if y.toBits >>> 32 >>> 31 == 1 then
        -Float.ofBits 0x3FF921FB54442D18 - Float.ofBits 0x01A56E1FC2F8F359
      else Float.ofBits 0x3FF921FB54442D18 + Float.ofBits 0x01A56E1FC2F8F359 := by
  unfold notNaN ixOf lxOf at *
  simp only [Atan.atan2, hn, h1, h2, h3, Bool.false_eq_true, ite_false, ite_true]
  try rfl

/-- `x = 1`: the result is `atan y`. -/
theorem atan2_one_eq (y x : Float) (hn : notNaN y x)
    (h1 : (x.toBits >>> 32 == 0x3ff00000 && lxOf x == 0) = true) :
    Atan.atan2 y x = Atan.atan y := by
  unfold notNaN ixOf lxOf at *
  simp only [Atan.atan2, hn, h1, Bool.false_eq_true, ite_false, ite_true]

end Verified.Examples.AtanTwoBranches
