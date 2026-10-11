import Verified.Examples.Asin
import LeanExe.ProofKit.F64UpperWord

/-!
The branches of `Asin.asin` and `Asin.acos` as equations.  `ixA x` is the high word of `|x|` and
`lxA x` the low word of `x`.  For `1/2 ≤ |x| < 1` both functions take `t = (1 - |x|)/2`,
`r = asinRatio t`, and `s = √t`; `bigTail` is `asin`'s form for `|x| ≥ 0.975` and `midTail` the
form with the split `s = w + c` below.
-/

namespace Verified.Examples.AsinTheoremBranches
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

def ixA (x : Float) : UInt64 := (x.toBits >>> 32) &&& 0x7fffffff

def lxA (x : Float) : UInt64 := x.toBits &&& 0xFFFFFFFF

def pio2HiF : Float := Float.ofBits 0x3FF921FB54442D18

def pio2LoF : Float := Float.ofBits 0x3C91A62633145C07

def pio4HiF : Float := Float.ofBits 0x3FE921FB54442D18

def tOf (x : Float) : Float := (1.0 - x.abs) * 0.5

def bigTail (t : Float) : Float :=
  pio2HiF - (2.0 * (t.sqrt + t.sqrt * Asin.asinRatio t) - pio2LoF)

def wOf (s : Float) : Float := Float.ofBits (s.toBits &&& 0xFFFFFFFF00000000)

def midTail (t : Float) : Float :=
  let s := t.sqrt
  let w := wOf s
  let c := (t - w * w) / (s + w)
  pio4HiF - ((2.0 * s * Asin.asinRatio t - (pio2LoF - 2.0 * c)) - (pio4HiF - 2.0 * w))

theorem asin_one_eq (x : Float) (h1 : ixA x ≥ 0x3ff00000)
    (h2 : (((ixA x - 0x3ff00000) ||| lxA x) == 0) = true) :
    Asin.asin x = x * pio2HiF + x * pio2LoF := by
  unfold ixA lxA at *
  simp only [Asin.asin, h1, h2, ite_true]
  rfl

theorem asin_tiny_eq (x : Float) (h1 : ¬ ixA x ≥ 0x3ff00000) (h2 : ixA x < 0x3fe00000)
    (h3 : ixA x < 0x3e500000) (hh : Float.ofBits 0x7E37E43C8800759C + x > 1.0) :
    Asin.asin x = x := by
  unfold ixA at *
  simp only [Asin.asin, h1, h2, h3, hh, ite_false, ite_true, decide_true, Bool.and_self]

theorem asin_small_eq (x : Float) (h1 : ¬ ixA x ≥ 0x3ff00000) (h2 : ixA x < 0x3fe00000)
    (h3 : ¬ ixA x < 0x3e500000) : Asin.asin x = x + x * Asin.asinRatio (x * x) := by
  unfold ixA at *
  simp only [Asin.asin, h1, h2, h3, ite_false, ite_true, decide_false, Bool.false_and,
    Bool.false_eq_true]

theorem asin_big_eq (x : Float) (h1 : ¬ ixA x ≥ 0x3ff00000) (h2 : ¬ ixA x < 0x3fe00000)
    (h3 : ixA x ≥ 0x3FEF3333) :
    Asin.asin x = if x.toBits >>> 32 >>> 31 == 0 then bigTail (tOf x) else -bigTail (tOf x) := by
  unfold ixA at *
  simp only [Asin.asin, h1, h2, h3, ite_false, ite_true]
  rfl

theorem asin_mid_eq (x : Float) (h1 : ¬ ixA x ≥ 0x3ff00000) (h2 : ¬ ixA x < 0x3fe00000)
    (h3 : ¬ ixA x ≥ 0x3FEF3333) :
    Asin.asin x = if x.toBits >>> 32 >>> 31 == 0 then midTail (tOf x) else -midTail (tOf x) := by
  unfold ixA at *
  simp only [Asin.asin, h1, h2, h3, ite_false, ite_true]
  rfl

end Verified.Examples.AsinTheoremBranches
