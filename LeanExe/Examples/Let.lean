namespace LeanExe.Examples.Let

def aliasLet : UInt64 :=
  let a := (Array.replicate 2 (0 : UInt64)).set! 0 11
  let b := a.set! 0 22
  b[0]! * (100 : UInt64) + a[0]!

def singleArrayUse : UInt64 :=
  let a := (Array.replicate 3 (0 : UInt64)).set! 1 7
  a[1]! + a[1]!

def boolLet (x : UInt64) : UInt64 :=
  let matched := x == 3
  if matched then 44 else 55

def letCondition (x : UInt64) : UInt64 :=
  if (let y := x + 1; y == 4) then 1 else 0

def recArgLetFuel : Nat → UInt64 → UInt64
  | 0, acc => acc
  | fuel + 1, acc => recArgLetFuel fuel (let next := acc + 2; next)

def recArgLetDemo : UInt64 :=
  recArgLetFuel 5 0

def branchArray (flag : UInt64) : UInt64 :=
  let a :=
    if flag == 0 then
      (Array.replicate 1 (0 : UInt64)).set! 0 5
    else
      (Array.replicate 1 (0 : UInt64)).set! 0 9
  a[0]!

def bumpAt (a : Array UInt64) (i : UInt64) : Array UInt64 :=
  let old := a[i.toNat]!
  a.set! i.toNat (old + 1)

def bumpDemo : UInt64 :=
  let a := Array.replicate 4 (0 : UInt64)
  let a := bumpAt a 2
  let a := bumpAt a 2
  a[2]!

def productLetPair : UInt64 :=
  let p := ((1 : UInt64), (2 : UInt64))
  p.1

end LeanExe.Examples.Let
