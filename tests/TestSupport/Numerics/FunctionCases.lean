import Library.Numerics.Float64.Log1p.Program
import Library.Numerics.Float64.Atan.Program
import Library.Numerics.Float64.Asin.Program
import Library.Numerics.Float64.Tan.Program
import Library.Numerics.Float64.Sinh.Program
import Library.Numerics.Float64.Asinh.Program
import Library.Numerics.Float64.Exp2.Program
import Library.Numerics.Float64.Log2.Program
import Library.Numerics.Float64.Log10.Program
import Library.Numerics.Float64.Pow.Program
import Library.Numerics.Float64.Sinpi.Program
import Library.Numerics.Float64.Erf.Program
import Library.Numerics.Float64.Erfc.Program
import Library.Numerics.Float64.Bessel.Program
import Library.Numerics.Float64.Tgamma.Program
import Library.Numerics.Float64.Lgamma.Program
import Library.Numerics.Decimal.ParseFloat.Program
import Library.Numerics.Decimal.PrintFloat.Program
import TestSupport.Host

/-! Module cases of the numerical functions whose modules no other case file covers: each export
at the special values, at points of its domain's boundary, and over a sweep of its range.  The
expected values come from native Lean. -/

namespace TestSupport.Numerics.FunctionCases

open TestSupport.Host Library.Numerics.Float64 Library.Numerics.Decimal

/-- Both zeros, the smallest subnormal, small and large magnitudes of each sign, both
infinities, and NaN. -/
def specials : List Float :=
  [0.0, -0.0, Float.ofBits 1, 1e-300, -1e-300, 1e-20, 0.5, -0.5, 1.0, -1.0, 2.0, -3.25, 10.0,
    100.0, 1e300, -1e300, inf, -inf, nan]

/-- `n` points from `a` with step `d`. -/
def sweep (a d : Float) (n : Nat) : List Float := (List.range n).map fun i => a + i.toFloat * d

def unary (m name : String) (f : Float → Float) (xs : List Float) : IO Unit :=
  for x in xs do
    line m name "f64" [fl x] s!"{(f x).toBits}"

def binary (m name : String) (f : Float → Float → Float) (xs : List (Float × Float)) : IO Unit :=
  for (x, y) in xs do
    line m name "f64" [fl x, fl y] s!"{(f x y).toBits}"

def pairs (xs ys : List Float) : List (Float × Float) := xs.flatMap fun x => ys.map (x, ·)

/-- The bytes of a text as words. -/
def text (s : String) : List UInt64 := s.toUTF8.toList.map (·.toUInt64)

def cases : IO Unit := do
  unary "log1p" "log1p" Log1p.log1p (specials ++ [-0.999, -1.5, 0.29, 0.41, 1e-9] ++
    sweep (-0.9) 0.37 30)
  unary "atan" "atan" Atan.atan (specials ++ [0.4375, 0.6875, 1.1875, 2.4375, 1e17] ++
    sweep (-20.0) 1.3 30)
  binary "atan" "atan2" Atan.atan2 (pairs [0.0, -0.0, 1.0, -1.0, 3.5, inf, -inf, nan]
    [0.0, -0.0, 1.0, -1.0, 0.25, inf, -inf, nan])
  for name in ["asin", "acos"] do
    unary "asin" name (if name == "asin" then Asin.asin else Asin.acos)
      (specials ++ [0.49, 0.5, 0.51, 0.975, 0.99999, -0.99999] ++ sweep (-1.0) 0.07 30)
  unary "tan" "tan" Tan.tan (specials ++ [0.6744, 0.7854, 1.5707963267948966, 3.141592653589793,
    1e6, 1e22] ++ sweep (-8.0) 0.55 30)
  for (name, f) in [("sinh", Sinh.sinh), ("cosh", Sinh.cosh)] do
    unary "sinh" name f (specials ++ [22.0, 710.0, 710.5, 711.0] ++ sweep (-30.0) 2.1 30)
  for (name, f) in [("asinh", Asinh.asinh), ("acosh", Asinh.acosh), ("atanh", Asinh.atanh)] do
    unary "asinh" name f (specials ++ [0.999, -0.999, 1.0000001, 2.5, 1e8, 3e8] ++
      sweep (-3.0) 0.21 30)
  for (name, f) in [("exp2", Exp2.exp2), ("exp10", Exp2.exp10)] do
    unary "exp2" name f (specials ++ [-1075.0, -1074.5, -1022.0, 1023.0, 1024.0, -323.5, 308.2,
      308.3] ++ sweep (-40.0) 2.7 30)
  unary "log2" "log2" Log2.log2 (specials ++ [0.9999, 1.0001, 3.0, 1024.0] ++ sweep 0.01 0.73 30)
  unary "log10" "log10" Log10.log10 (specials ++ [0.9999, 1.0001, 1000.0, 1e-5] ++
    sweep 0.01 0.73 30)
  binary "pow" "pow" Pow.pow (pairs [0.0, -0.0, 0.5, -0.5, 1.0, -1.0, 2.0, -2.0, 1e300, inf, -inf,
    nan] [0.0, -0.0, 0.5, 1.0, -1.0, 2.0, 3.0, -3.0, 1e10, 0.3333333333333333, inf, -inf, nan])
  for (name, f) in [("sinpi", Sinpi.sinpi), ("cospi", Sinpi.cospi), ("tanpi", Sinpi.tanpi)] do
    unary "sinpi" name f (specials ++ [0.25, 0.75, 1.5, -2.5, 4503599627370496.0] ++
      sweep (-3.0) 0.19 30)
  unary "erf" "erf" Erf.erf (specials ++ [0.84375, 1.25, 2.857, 6.0, 5.9] ++ sweep (-4.0) 0.27 30)
  unary "erfc" "erfc" Erfc.erfc (specials ++ [0.84375, 1.25, 2.857, 6.0, 27.2, 28.0] ++
    sweep (-4.0) 1.1 30)
  for (name, f) in [("j0", Bessel.j0), ("j1", Bessel.j1), ("y0", Bessel.y0), ("y1", Bessel.y1)] do
    unary "bessel" name f (specials ++ [2.404825557695773, 3.8317, 0.8935769662791675] ++
      sweep 0.1 1.7 30)
  for n in [(0 : UInt64), 1, 2, 5, 40] do
    for x in [0.0, -0.0, 0.5, -2.0, 3.0, 50.0, 1e300, inf, nan] do
      line "bessel" "jn" "f64" [u n, fl x] s!"{(Bessel.jn n x).toBits}"
      line "bessel" "yn" "f64" [u n, fl x] s!"{(Bessel.yn n x).toBits}"
  unary "tgamma" "tgamma" Tgamma.tgamma (specials ++ [-2.5, -170.5, 171.6, 171.7, 3.0] ++
    sweep (-5.3) 0.6 30)
  unary "lgamma" "lgamma" Lgamma.lgamma (specials ++ [-2.5, 2.0, 3.0, 1e17, 2.5e305] ++
    sweep (-5.3) 0.6 30)
  for x in specials ++ [-2.5, -3.5] do
    let r := Lgamma.lgammaR x
    line "lgamma" "lgammaR" "list:f64,f64" [fl x] s!"{r.1.toBits} {r.2.toBits}"
  for s in ["0", "-0", "1", "1.5", "1e400", "-1e400", "4.9e-324", "2.5e-324", "0.1",
      "9007199254740993", "1.7976931348623157e308", "1.7976931348623159e308", "abc", "1.",
      ".5", "1e", "0x1p-3", "inf", "-Infinity", "nan", "+3", "15.50103472"] do
    for general in [false, true] do
      let a := arrU (text s)
      let g := if general then "i64:1" else "i64:0"
      let r := ParseFloat.parse64 general (text s).toArray
      line "parsefloat" "parse64" "list:i64,i64" [g, a] s!"{if r.1 then 1 else 0} {r.2}"
      let r := ParseFloat.parse32 general (text s).toArray
      line "parsefloat" "parse32" "list:i64,i64" [g, a] s!"{if r.1 then 1 else 0} {r.2}"
  for x in specials ++ [0.1, 1e21, 1e-7, 123456789.0, 5e-324] do
    for (name, f) in [("print64", PrintFloat.print64), ("print64Ecma", PrintFloat.print64Ecma)] do
      line "printfloat" name "array-u64" [u x.toBits] (words (f x.toBits).toList)
  for w in ([0, 0x80000000, 1, 0x3dcccccd, 0x3f800000, 0x7f7fffff, 0x7f800000, 0xff800000,
      0x7fc00000] : List UInt64) do
    for (name, f) in [("print32", PrintFloat.print32), ("print32Ecma", PrintFloat.print32Ecma)] do
      line "printfloat" name "array-u64" [u w] (words (f w).toList)

end TestSupport.Numerics.FunctionCases
