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

verified_compile compiled := [identity, mixed, read, same, replace, push, borrowedPush, duplicate, collect,
  build, paired, literal, count]

theorem same_owned : LeanExe.Pipeline.ImplementsA true compiled.module 5
    (fun x : LeanExe.Pipeline.Moved (Array Float32) => same x.val) (fun _ _ _ => True)
    (fun _ _ _ _ _ => True) := compiled.same.implements

theorem borrowedPush_borrowed : LeanExe.Pipeline.ImplementsA true compiled.module 8
    (fun p : Array Float32 × Float32 => borrowedPush p.1 p.2) (fun _ _ _ => True)
    (fun _ _ _ _ _ => True) := compiled.borrowedPush.implements

#print axioms compiled.bytes
#print axioms compiled.count.bound_eq
#print axioms compiled.push.trapFree
#print axioms same_owned
#print axioms borrowedPush_borrowed

end Verified.Examples.Floats32
