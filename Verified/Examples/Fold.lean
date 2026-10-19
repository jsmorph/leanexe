import Verified.Reflect.Command

namespace Verified.Examples.Fold

def words (xs : Array UInt64) (seed : UInt64) : UInt64 :=
  xs.foldl (fun acc value => acc * 3 + value) seed

def floats (xs : Array Float) (seed : Float) : Float :=
  xs.foldl (fun acc value => acc + value) seed

structure Entry where
  key : UInt64
  price : Float
  active : Bool

instance : LeanExe.Pipeline.Flat Entry (UInt64 × Float × Bool) :=
  ⟨fun e => (e.key, e.price, e.active)⟩

def records (xs : Array Entry) : Entry :=
  xs.foldl (fun acc value =>
    ⟨acc.key + value.key, acc.price + value.price, acc.active && value.active⟩)
    ⟨0, 0, true⟩

def owned (xs seed : Array UInt64) : Array UInt64 :=
  xs.foldl (fun acc value => acc.push value) seed

def pair (xs : Array UInt64) : UInt64 × Array UInt64 :=
  xs.foldl (fun acc value => (acc.1 + value, acc.2.push value)) (0, #[])

def nested (xs : Array UInt64) : UInt64 :=
  xs.foldl (fun acc value =>
    acc + (LeanExe.build value fun i => i).foldl (fun total n => total + n) 0) 0

def helper (x : UInt64) : UInt64 := x * 5 + 1

def calls (xs : Array UInt64) : UInt64 :=
  xs.foldl (fun acc value => acc + helper value) 0

verified_compile compiled := [words, floats, records, owned, pair, nested, helper, calls]

#print axioms compiled.words.denote_eq
#print axioms compiled.records.implements
#print axioms compiled.owned.trapFree
#print axioms compiled.pair.implements
#print axioms compiled.nested.implements
#print axioms compiled.bytes

end Verified.Examples.Fold
