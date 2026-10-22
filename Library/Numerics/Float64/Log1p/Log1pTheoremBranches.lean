import Library.Numerics.Float64.Log1p.Compiled
import Library.Numerics.Float64.Log.LogCoreBits
import LeanExe.ProofKit.F64UpperWord

/-!
The branches of `Log1p.log1p` and `Log1p.log1pTail` as equations.  `hxOf x` is the high word of
`x` and `axOf x` that of `|x|`.  Below `2 ^ -29` in magnitude the result is `x` or `x - x x/2`,
on `[-0.2929, 0.4142)` it is `log1pTail x 0 0 1`, and elsewhere it is `mainTail u c k`, which
normalizes `u` to `1 + f` with `√2/2 ≤ 1 + f < √2` and calls `log1pTail`.  `u` is `1 + x` with
the correction `cOf x u / u` below `2 ^ 53`, and `x` with correction 0 from there on.
`log1pTail` computes `f - (f²/2 - s (f²/2 + R))` for `k = 0` and adds `k ln 2` in two parts
otherwise.
-/

namespace Library.Numerics.Float64.Log1p.Log1pTheoremBranches
open CodeLib.IEEE64 LeanExe.ProofKit

set_option exponentiation.threshold 4096

def hxOf (x : Float) : UInt64 := x.toBits >>> 32

def axOf (x : Float) : UInt64 := hxOf x &&& 0x7fffffff

def hfsqOf (f : Float) : Float := 0.5 * f * f

def sOf (f : Float) : Float := f / (2.0 + f)

def ROf (f : Float) : Float :=
  let z := sOf f * sOf f
  z * (Float.ofBits 0x3FE5555555555593 + z * (Float.ofBits 0x3FD999999997FA04 +
    z * (Float.ofBits 0x3FD2492494229359 + z * (Float.ofBits 0x3FCC71C51D8E78AF +
    z * (Float.ofBits 0x3FC7466496CB03DE + z * (Float.ofBits 0x3FC39A09D078C69F +
    z * Float.ofBits 0x3FC2F112DF3E5244))))))

def POf (f : Float) : Float := sOf f * (hfsqOf f + ROf f)

def RqOf (f : Float) : Float := hfsqOf f * (1.0 - Float.ofBits 0x3FE5555555555555 * f)

def ln2HiF : Float := Float.ofBits 0x3FE62E42FEE00000

def ln2LoF : Float := Float.ofBits 0x3DEA39EF35793C76

theorem tail_k0_eq (f c : Float) (hu : UInt64) (h : (hu == 0) = false) :
    Log1p.log1pTail f c 0 hu = f - (hfsqOf f - POf f) := by
  simp only [Log1p.log1pTail, h, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true]
  rfl

theorem tail_s_eq (f c : Float) (k hu : UInt64) (hk : (k == 0) = false)
    (h : (hu == 0) = false) :
    Log1p.log1pTail f c k hu =
      Library.Numerics.Float64.Log.LogCoreBits.kdOf k * ln2HiF - ((hfsqOf f - (POf f + (Library.Numerics.Float64.Log.LogCoreBits.kdOf k * ln2LoF + c))) - f) := by
  simp only [Log1p.log1pTail, h, hk, Bool.false_eq_true, ite_false]
  rfl

theorem tail_q_eq (f c : Float) (k hu : UInt64) (hk : (k == 0) = false) (h : (hu == 0) = true)
    (hf : (f == 0.0) = false) :
    Log1p.log1pTail f c k hu = Library.Numerics.Float64.Log.LogCoreBits.kdOf k * ln2HiF - ((RqOf f - (Library.Numerics.Float64.Log.LogCoreBits.kdOf k * ln2LoF + c)) - f) := by
  simp only [Log1p.log1pTail, h, hk, hf, Bool.false_eq_true, ite_false, ite_true]
  rfl

theorem tail_z_eq (f c : Float) (k hu : UInt64) (hk : (k == 0) = false) (h : (hu == 0) = true)
    (hf : (f == 0.0) = true) :
    Log1p.log1pTail f c k hu = Library.Numerics.Float64.Log.LogCoreBits.kdOf k * ln2HiF + (c + Library.Numerics.Float64.Log.LogCoreBits.kdOf k * ln2LoF) := by
  simp only [Log1p.log1pTail, h, hk, hf, Bool.false_eq_true, ite_false, ite_true]
  rfl

def kOf (u : Float) : UInt64 := ((u.toBits >>> 32) >>> 20) - 1023

def cOf (x u : Float) : Float :=
  if kOf u >>> 63 == 0 && kOf u != 0 then 1.0 - (u - x) else x - (u - 1.0)

def mainTail (u c : Float) (k : UInt64) : Float :=
  let hu := (u.toBits >>> 32) &&& 0x000fffff
  let low := u.toBits &&& 0xFFFFFFFF
  if hu < 0x6a09e then
    Log1p.log1pTail (Float.ofBits (((hu ||| 0x3ff00000) <<< 32) ||| low) - 1.0) c k hu
  else
    Log1p.log1pTail (Float.ofBits (((hu ||| 0x3fe00000) <<< 32) ||| low) - 1.0) c (k + 1)
      ((0x00100000 - hu) >>> 2)

theorem log1p_tiny_eq (x : Float) (h1 : (hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) = true)
    (h2 : axOf x < 0x3e200000) :
    Log1p.log1p x = if (Float.ofBits 0x4350000000000000 + x > 0.0 && axOf x < 0x3c900000) then x
      else x - x * x * 0.5 := by
  have h3 : ¬ axOf x ≥ 0x3ff00000 := by
    intro h
    have a := UInt64.lt_iff_toNat_lt.mp h2
    have b := UInt64.le_iff_toNat_le.mp h
    simp at a b
    omega
  unfold axOf hxOf at *
  simp only [Log1p.log1p, h1, h2, h3, decide_false, decide_true, Bool.and_false, Bool.and_true,
    Bool.true_and, Bool.false_eq_true, ite_false, ite_true]

theorem log1p_k0_eq (x : Float) (h1 : (hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) = true)
    (h2 : ¬ axOf x < 0x3e200000) (h3 : ¬ axOf x ≥ 0x3ff00000)
    (h4 : ((!(hxOf x >>> 31 == 1) && hxOf x != 0) ||
      (hxOf x >>> 31 == 1 && hxOf x ≤ 0xbfd2bec4)) = true) :
    Log1p.log1p x = Log1p.log1pTail x 0.0 0 1 := by
  unfold axOf hxOf at *
  simp only [Log1p.log1p, h1, h2, h3, h4, decide_false, Bool.and_false, Bool.true_and,
    Bool.false_eq_true, ite_false, ite_true]

theorem log1p_main_eq (x : Float)
    (h1 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) && axOf x ≥ 0x3ff00000) = false)
    (h2 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) && axOf x < 0x3e200000) = false)
    (h3 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) &&
      ((!(hxOf x >>> 31 == 1) && hxOf x != 0) ||
        (hxOf x >>> 31 == 1 && hxOf x ≤ 0xbfd2bec4))) = false)
    (h4 : (!(hxOf x >>> 31 == 1) && hxOf x ≥ 0x7ff00000) = false)
    (h5 : (hxOf x >>> 31 == 1 || hxOf x < 0x43400000) = true) :
    Log1p.log1p x = mainTail (1.0 + x) (cOf x (1.0 + x) / (1.0 + x)) (kOf (1.0 + x)) := by
  unfold axOf hxOf at *
  simp only [Log1p.log1p, h1, h2, h3, h4, h5, Bool.false_eq_true, ite_false, ite_true]
  rfl

theorem log1p_big_eq (x : Float)
    (h1 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) && axOf x ≥ 0x3ff00000) = false)
    (h2 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) && axOf x < 0x3e200000) = false)
    (h3 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) &&
      ((!(hxOf x >>> 31 == 1) && hxOf x != 0) ||
        (hxOf x >>> 31 == 1 && hxOf x ≤ 0xbfd2bec4))) = false)
    (h4 : (!(hxOf x >>> 31 == 1) && hxOf x ≥ 0x7ff00000) = false)
    (h5 : (hxOf x >>> 31 == 1 || hxOf x < 0x43400000) = false) :
    Log1p.log1p x = mainTail x 0.0 (kOf x) := by
  unfold axOf hxOf at *
  simp only [Log1p.log1p, h1, h2, h3, h4, h5, Bool.false_eq_true, ite_false, ite_true]
  rfl

theorem log1p_b1_eq (x : Float)
    (h1 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) && axOf x ≥ 0x3ff00000) = true) :
    Log1p.log1p x =
      if x == -1.0 then -Float.ofBits 0x4350000000000000 / 0.0 else (x - x) / (x - x) := by
  unfold axOf hxOf at *
  simp only [Log1p.log1p, h1, ite_true]

theorem log1p_b4_eq (x : Float)
    (h1 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) && axOf x ≥ 0x3ff00000) = false)
    (h2 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) && axOf x < 0x3e200000) = false)
    (h3 : ((hxOf x >>> 31 == 1 || hxOf x < 0x3FDA827A) &&
      ((!(hxOf x >>> 31 == 1) && hxOf x != 0) ||
        (hxOf x >>> 31 == 1 && hxOf x ≤ 0xbfd2bec4))) = false)
    (h4 : (!(hxOf x >>> 31 == 1) && hxOf x ≥ 0x7ff00000) = true) :
    Log1p.log1p x = x + x := by
  unfold axOf hxOf at *
  simp only [Log1p.log1p, h1, h2, h3, h4, Bool.false_eq_true, ite_false, ite_true]

end Library.Numerics.Float64.Log1p.Log1pTheoremBranches
