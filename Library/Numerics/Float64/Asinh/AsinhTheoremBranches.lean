import Library.Numerics.Float64.Asinh.Compiled
import Library.Numerics.Float64.Atan.AtanTheorem

/-!
The branches of `Asinh.asinh` and `Asinh.acosh` as equations.  `ixOf x` is the
high word of `|x|` (`Library.Numerics.Float64.Atan.AtanTheoremBranches.ixOf`), and `hxOf x` the high word of `x`.  `asinhW x` is
the value of `asinh |x|` before the sign: `log |x| + ln2` above `2 ^ 28`, `log (2 |x| + 1/(√(x² + 1)
+ |x|))` above 2, and `log1p (|x| + x²/(1 + √(1 + x²)))` below.  The branches of `Asinh.atanh` are
in `AtanhTheoremBranches`.
-/

namespace Library.Numerics.Float64.Asinh.AsinhTheoremBranches
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Atan.AtanTheoremBranches

set_option exponentiation.threshold 4096

def ln2F : Float := Float.ofBits 0x3FE62E42FEFA39EF

def hxOf (x : Float) : UInt64 := x.toBits >>> 32

def asinhW (x : Float) : Float :=
  if ixOf x > 0x41b00000 then Log.log x.abs + ln2F
  else if ixOf x > 0x40000000 then Log.log (2.0 * x.abs + 1.0 / ((x * x + 1.0).sqrt + x.abs))
  else Log1p.log1p (x.abs + x * x / (1.0 + (1.0 + x * x).sqrt))

theorem asinh_tiny_eq (x : Float) (h1 : ixOf x < 0x3e300000)
    (hh : Float.ofBits 0x7E37E43C8800759C + x > 1.0) : Asinh.asinh x = x := by
  have h0 : ¬ ixOf x ≥ 0x7ff00000 := by
    intro h
    have a := UInt64.lt_iff_toNat_lt.mp h1
    have b := UInt64.le_iff_toNat_le.mp h
    simp at a b
    omega
  unfold ixOf at h0 h1
  simp only [Asinh.asinh, Asinh.asinhWith, h0, h1, hh, ite_false, ite_true, decide_true,
    Bool.and_true]

theorem asinh_main_eq (x : Float) (h0 : ¬ ixOf x ≥ 0x7ff00000) (h1 : ¬ ixOf x < 0x3e300000) :
    Asinh.asinh x = if x.toBits >>> 32 >>> 31 == 0 then asinhW x else -asinhW x := by
  unfold ixOf at h0 h1
  simp only [Asinh.asinh, Asinh.asinhWith, h0, h1, ite_false, decide_false, Bool.false_and,
    Bool.false_eq_true]
  rfl

theorem acosh_log2_eq (x : Float) (h1 : (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000) = false)
    (h2 : hxOf x ≥ 0x41b00000) (h3 : ¬ hxOf x ≥ 0x7ff00000) :
    Asinh.acosh x = Log.log x + ln2F := by
  unfold hxOf at h1 h2 h3
  simp only [Asinh.acosh, Asinh.acoshWith, h1, h2, h3, Bool.false_eq_true, ite_false, ite_true]
  rfl

theorem acosh_one_eq (x : Float) (h1 : (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000) = false)
    (h2 : ¬ hxOf x ≥ 0x41b00000)
    (h3 : (((hxOf x - 0x3ff00000) ||| (x.toBits &&& 0xFFFFFFFF)) == 0) = true) :
    Asinh.acosh x = 0.0 := by
  unfold hxOf at h1 h2 h3
  simp only [Asinh.acosh, Asinh.acoshWith, h1, h2, h3, Bool.false_eq_true, ite_false, ite_true]

theorem acosh_mid_eq (x : Float) (h1 : (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000) = false)
    (h2 : ¬ hxOf x ≥ 0x41b00000)
    (h3 : (((hxOf x - 0x3ff00000) ||| (x.toBits &&& 0xFFFFFFFF)) == 0) = false)
    (h4 : hxOf x > 0x40000000) :
    Asinh.acosh x = Log.log (2.0 * x - 1.0 / (x + (x * x - 1.0).sqrt)) := by
  unfold hxOf at h1 h2 h3 h4
  simp only [Asinh.acosh, Asinh.acoshWith, h1, h2, h3, h4, Bool.false_eq_true, ite_false,
    ite_true]
  rfl

theorem acosh_small_eq (x : Float) (h1 : (hxOf x >>> 31 == 1 || hxOf x < 0x3ff00000) = false)
    (h2 : ¬ hxOf x ≥ 0x41b00000)
    (h3 : (((hxOf x - 0x3ff00000) ||| (x.toBits &&& 0xFFFFFFFF)) == 0) = false)
    (h4 : ¬ hxOf x > 0x40000000) :
    Asinh.acosh x =
      Log1p.log1p ((x - 1.0) + (2.0 * (x - 1.0) + (x - 1.0) * (x - 1.0)).sqrt) := by
  unfold hxOf at h1 h2 h3 h4
  simp only [Asinh.acosh, Asinh.acoshWith, h1, h2, h3, h4, Bool.false_eq_true, ite_false]

end Library.Numerics.Float64.Asinh.AsinhTheoremBranches
