import Verified.Examples.Uscale

/-! A native check of `Uscale`'s routines against Lean's `Nat` on pseudo-random operands of up to
120 limbs: `mulSmall`, `shl`, `le`, `sub`, `bitLen`, `divBits`, `scaledQuot`, and `pow10`.  The
theorems of `UscaleTheorem` prove the same equations; the check runs the compiled native code and
exits with an error at the first difference.  Run with `lake env lean --run`. -/

namespace Verified.Examples.UscaleCheck
open Uscale

def valOf (a : Array UInt64) : Nat := a.foldr (fun x acc => x.toNat + 2 ^ 32 * acc) 0

def ofNat (v : Nat) (n : Nat) : Array UInt64 :=
  (List.range n).toArray.map fun i => UInt64.ofNat (v / 2 ^ (32 * i) % 2 ^ 32)

/-- The `i`th word of a SplitMix64 stream. -/
def word (seed i : Nat) : UInt64 :=
  let z := UInt64.ofNat i * 0x9e3779b97f4a7c15 + UInt64.ofNat seed * 0x632be59bd9b4e019
  let z := (z ^^^ (z >>> 30)) * 0xbf58476d1ce4e5b9
  let z := (z ^^^ (z >>> 27)) * 0x94d049bb133111eb
  z ^^^ (z >>> 31)

def number (seed limbs : Nat) : Nat :=
  (List.range limbs).foldl (fun acc i => acc * 2 ^ 32 + (word seed i).toNat % 2 ^ 32) 0

def check (name : String) (ok : Bool) (count : IO.Ref Nat) : IO Unit := do
  count.modify (· + 1)
  unless ok do
    throw (IO.userError s!"{name} differs")

def main : IO Unit := do
  let count ← IO.mkRef 0
  for t in [0:400] do
    let la := 1 + (word 1 t).toNat % 120
    let lb := 1 + (word 2 t).toNat % 120
    let x := number (3 + t) la
    let y := number (5000 + t) lb
    let a := ofNat x la
    let b := ofNat y lb
    let m := (word 4 t) &&& 0xFFFFFFFF
    let c := (word 6 t) &&& 0xFFFFFFFF
    check "mulSmall" (valOf (mulSmall a m c) == x * m.toNat + c.toNat) count
    let k := (word 7 t) % 2000
    check "shl" (valOf (shl a k) == x * 2 ^ k.toNat) count
    check "le" (le a b == decide (x ≤ y)) count
    check "le self" (le a a) count
    if y ≤ x then check "sub" (valOf (sub a b) == x - y) count
    else check "sub" (valOf (sub b a) == y - x) count
    check "bitLen" ((bitLen a).toNat == (if x = 0 then 0 else Nat.log2 x + 1)) count
    let bits := 1 + (word 8 t) % 63
    let d := if y == 0 then 1 else y
    let n := (x % (d * 2 ^ bits.toNat))
    let r := divBits (ofNat n (la + lb + 3)) (ofNat d lb) bits
    check "divBits quotient" (r.1.toNat == n / d) count
    check "divBits remainder" (valOf r.2 == n % d) count
    let sn := (word 9 t) % 300
    let sd := (word 10 t) % 300
    let num := x / 2 ^ 64 + 1
    let den := y + 1
    if num * 2 ^ sn.toNat < den * 2 ^ sd.toNat * 2 ^ 63 then
      let q := scaledQuot (ofNat num la) (ofNat den (lb + 1)) sn sd 63
      check "scaledQuot quotient" (q.1.toNat == num * 2 ^ sn.toNat / (den * 2 ^ sd.toNat)) count
      check "scaledQuot remainder" (q.2 == (num * 2 ^ sn.toNat % (den * 2 ^ sd.toNat) != 0)) count
  for k in [0:400] do
    check "pow10" (valOf (pow10 (UInt64.ofNat k)) == 10 ^ k) count
  IO.println s!"{← count.get} results equal Lean's Nat"

end Verified.Examples.UscaleCheck

def main : IO Unit := Verified.Examples.UscaleCheck.main
