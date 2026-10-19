import Verified.Reflect.Command

namespace Verified.Examples.Floats32

def identity (x : Float32) : Float32 := x

def mixed (x : Float32) (y : Float) (n : UInt64) : Float × Float32 × UInt64 :=
  (y, x, n)

def read (xs : Array Float32) (i : UInt64) : Float32 := xs[i.toNat]!

def same (xs : Array Float32) : Array Float32 := xs

def replace (xs : Array Float32) (i : UInt64) (x : Float32) : Array Float32 :=
  xs.set! i.toNat x

def push (xs : Array Float32) (x : Float32) : Array Float32 := xs.push x

def borrowedPush (xs : Array Float32) (x : Float32) : Array Float32 × UInt64 :=
  (xs.push x, xs.size.toUInt64)

def duplicate (xs : Array Float32) : Array Float32 × Array Float32 := (xs, xs)

def collect (xs : Array Float32) : Array Float32 :=
  xs.foldl (fun acc x => acc.push x) #[]

def build (n : UInt64) (x : Float32) : Array Float32 := LeanExe.build n fun _ => x

structure PairValue where
  lo : Float32
  hi : Float
  deriving Inhabited

instance : LeanExe.Pipeline.Flat PairValue (Float32 × Float) := ⟨fun p => (p.lo, p.hi)⟩

def paired (xs : Array PairValue) (i : UInt64) : PairValue := xs[i.toNat]!

def literal (tag : UInt64) : Float32 :=
  if tag = 0 then 0.0
  else if tag = 1 then -0.0
  else if tag = 2 then 1.25
  else if tag = 3 then Float32.ofBits 0x7f800001
  else if tag = 4 then -(Float32.ofBits 0xffc00001)
  else if tag = 5 then Float32.ofBits 1
  else if tag = 6 then (18446744073709551615 : UInt64).toFloat32
  else 1

def count (n : UInt64) (x : Float32) : Float32 :=
  if n = 0 then x else count (n - 1) x
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def arithmetic (a b c : Float32) : Float32 := ((a + b) * c - a) / (b - c)

def piecewise (x lo hi : Float32) : Float32 :=
  if x < lo then -(lo - x) * 0.5
  else if x ≤ hi then (x - lo).abs + min x hi
  else max (x * 2) hi - 1.5

def hypot (x y s : Float32) : Float32 := (x * x + y * y).sqrt / s

def inBand (x lo hi : Float32) : Bool := (lo ≤ x && x < hi) || (x == hi && lo != hi)

def clamp (x lo hi : Float32) : Float32 := if x < lo then lo else if x > hi then hi else x

def negate (x : Float32) : Float32 := -x

def absolute (x : Float32) : Float32 := x.abs

def nearest (x : Float32) : Float32 := LeanExe.Float32.nearest x

def least (a b : Float32) : Float32 := min a b

def most (a b : Float32) : Float32 := max a b

def convert (w : UInt64) : Float32 := w.toFloat32

def ofBits (w : UInt64) : Float32 := Float32.ofBits w.toUInt32

def bits (x : Float32) : UInt64 := x.toBits.toUInt64

def truncate (x : Float32) : UInt64 := x.toUInt64

def signedConvert (w : UInt64) : Float32 := (Int32.ofUInt32 w.toUInt32).toFloat32

def signedTruncate (x : Float32) : UInt64 := x.toInt32.toUInt32.toUInt64

def roundTrip (w : UInt64) : UInt64 := (Float32.ofBits w.toUInt32).toBits.toUInt64

def affine (xs : Array Float32) (a b : Float32) : Array Float32 :=
  LeanExe.build xs.size.toUInt64 fun i => a * xs[i.toNat]! + b

def total (xs : Array Float32) (seed : Float32) : Float32 := xs.foldl (· + ·) seed

def indexSum (n : UInt64) (x : Float32) : Float32 :=
  LeanExe.loop n x fun i acc => acc + i.toFloat32 * 0.25

def guarded (n : UInt64) (x : Float32) : Float32 :=
  if n = 0 then x else guarded (n - 1) x + 1.0
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def tailSign (n : UInt64) (x : Float32) : Float32 :=
  if n = 0 then x
  else if x < 0 then tailSign (n - 1) (-x)
  else tailSign (n - 1) (x + 0.25)
termination_by n.toNat
decreasing_by
  all_goals
    rename_i hn _
    simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
    omega

def deep (n : UInt64) (a : Float32) (b : Float) : Float32 × Float × UInt64 :=
  if n = 0 then (a, b, 0) else
    let x0 := a + 1
    let x1 := b + 1
    let x2 := x0 * 0.5
    let x3 := x1 * 0.5
    let x4 := x2 + 2
    let x5 := x3 + 2
    let x6 := x4 * 0.5
    let x7 := x5 * 0.5
    let x8 := x6 + 3
    let x9 := x7 + 3
    let x10 := x8 * 0.5
    let x11 := x9 * 0.5
    let x12 := x10 + 4
    let x13 := x11 + 4
    let x14 := x12 * 0.5
    let x15 := x13 * 0.5
    let x16 := x14 + 5
    let x17 := x15 + 5
    let x18 := x16 * 0.5
    let x19 := x17 * 0.5
    let x20 := x18 + 6
    let x21 := x19 + 6
    let r := deep (n - 1) x20 x21
    (r.1 + x0 + x2 + x4 + x6 + x8 + x10 + x12 + x14 + x16 + x18 + x20,
      r.2.1 + x1 + x3 + x5 + x7 + x9 + x11 + x13 + x15 + x17 + x19 + x21,
      r.2.2 + 1)
termination_by n.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega


verified_compile compiled := [identity, mixed, read, same, replace, push, borrowedPush, duplicate, collect,
  build, paired, literal, count, arithmetic, piecewise, hypot, inBand, clamp, negate, absolute,
  nearest, least, most, convert, ofBits, bits, truncate, signedConvert, signedTruncate, roundTrip,
  affine, total, indexSum, guarded, tailSign, deep]

set_option maxRecDepth 4096 in
example : Verified.positions compiled.deep.func.body true = 32 := rfl

theorem same_owned : LeanExe.Pipeline.ImplementsA true compiled.module 5
    (fun x : LeanExe.Pipeline.Moved (Array Float32) => same x.val) (fun _ _ _ => True)
    (fun _ _ _ _ _ => True) := compiled.same.implements

theorem borrowedPush_borrowed : LeanExe.Pipeline.ImplementsA true compiled.module 8
    (fun p : Array Float32 × Float32 => borrowedPush p.1 p.2) (fun _ _ _ => True)
    (fun _ _ _ _ _ => True) := compiled.borrowedPush.implements

#print axioms compiled.bytes
#print axioms compiled.count.bound_eq
#print axioms compiled.push.trapFree
#print axioms compiled.tailSign.bound_eq
#print axioms compiled.guarded.fits_eq
#print axioms compiled.deep.fits_eq
#print axioms same_owned
#print axioms borrowedPush_borrowed

end Verified.Examples.Floats32
