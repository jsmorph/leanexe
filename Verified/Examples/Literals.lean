import Verified.Reflect.Command

namespace Verified.Examples.Literals

open LeanExe

def constant : Bytes := bytes![65, 0, 255]

def empty : Bytes := bytes![]

def repeated : Bytes × Bytes := (bytes![65, 0, 255], bytes![65, 0, 255])

def choose (condition : Bool) : Bytes :=
  if condition then bytes![65, 0, 255] else bytes![128, 1]

def lookup (index : UInt64) : UInt64 := (bytes![65, 0, 255]).get index

def helper (index : UInt64) : UInt64 := lookup index

def nestedIndex (bytes : Bytes) : UInt64 := bytes.get ((bytes![1]).get 0)

def byteBuild (count : UInt64) : Bytes :=
  Bytes.build count fun index => (bytes![65, 0, 255]).get (index % 3)

def arrayBuild (count : UInt64) : Array UInt64 :=
  LeanExe.build count fun index => (bytes![65, 0, 255]).get (index % 3)

def loop (count : UInt64) : UInt64 :=
  LeanExe.loop count 0 fun index acc => acc + (bytes![65, 0, 255]).get (index % 3)

def arrayFold (values : Array UInt64) : UInt64 :=
  values.foldl (fun acc value => acc + (bytes![65, 0, 255]).get (value % 3)) 0

def listFold (values : List UInt64) : UInt64 :=
  values.foldl (fun acc value => acc + (bytes![65, 0, 255]).get (value % 3)) 0

def treeCase (values : List UInt64) : UInt64 :=
  match values with
  | [] => (bytes![65, 0, 255]).get 0
  | first :: _ => (bytes![128, 1]).get (first % 2)

def tail (count : UInt64) (value : Bytes) : Bytes :=
  if count = 0 then value else tail (count - 1) (bytes![65, 0, 255])
termination_by count.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

def guarded (count : UInt64) : UInt64 :=
  if count = 0 then 0 else guarded (count - 1) + (bytes![65, 0, 255]).get (count % 3)
termination_by count.toNat
decreasing_by
  rename_i hn
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
  omega

verified_compile compiled :=
  [constant, empty, repeated, choose, lookup, helper, nestedIndex, byteBuild, arrayBuild, loop, arrayFold,
    listFold, treeCase, tail, guarded]

example : compiled.literalPool.values = [[65, 0, 255], [128, 1], [1]] := by decide +kernel

#print axioms compiled.bytes

end Verified.Examples.Literals
