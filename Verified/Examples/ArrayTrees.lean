import Verified.Reflect.Command

/-! A recursive type whose records hold an array of words beside a word and two children.  A
record holds its word and child slots in the order of the fields and then its array slot, as the
`Encode` instance states.  A construction moves an array into a record, a borrowed array argument
as a copy, a match binds the array as a variable, an owned match moves it out of the record and
releases it when the branch does not use it, and a copy of a borrowed tree copies the array of
each record. -/

namespace Verified.Examples.ArrayTrees

open LeanExe.Pipeline

/-- Buckets in a tree: nothing, or a bucket with a key and its items between two subtrees. -/
inductive Buckets where
  | empty
  | bucket (left : Buckets) (key : UInt64) (items : Array UInt64) (right : Buckets)

/-- `Buckets` as records: `empty` is the null pointer, and a bucket a record of its left child, its
key, and its right child, followed by its items. -/
def Buckets.encode : Buckets → Node
  | .empty => .null
  | .bucket l k xs r => .record [.child l.encode, .word k, .child r.encode, .array xs]

instance : Encode Buckets := ⟨Buckets.encode⟩

verified_recursive_type Buckets

def keep (t : Buckets) : Buckets := t

def single (k : UInt64) (xs : Array UInt64) : Buckets := .bucket .empty k xs .empty

/-- The number of items in the tree. -/
def count : Buckets → UInt64
  | .empty => 0
  | .bucket l _ xs r => count l + xs.size.toUInt64 + count r

/-- The sum of the keys, whose owned matches release the items. -/
def keys : Buckets → UInt64
  | .empty => 0
  | .bucket l k _ r => keys l + k + keys r

/-- The sum of the items of the root bucket. -/
def rootSum : Buckets → UInt64
  | .empty => 0
  | .bucket _ _ xs _ => LeanExe.loop xs.size.toUInt64 0 fun i acc => acc + xs[i.toNat]!

/-- The tree with `x` pushed onto the items of every bucket, which reuses each record. -/
def pushAll (x : UInt64) : Buckets → Buckets
  | .empty => .empty
  | .bucket l k xs r => .bucket (pushAll x l) k (xs.push x) (pushAll x r)

/-- Three buckets of the items `xs`, each holding its own copy. -/
def three (xs : Array UInt64) : Buckets := .bucket (single 1 xs) 2 xs (single 3 xs)

/-- The items of `three xs` after a push of `x`, counted on a copy of the tree. -/
def grown (xs : Array UInt64) (x : UInt64) : UInt64 :=
  let t := pushAll x (three xs)
  count (keep t) + keys t

/-- The root sum of `three xs` after a push of `x`. -/
def grownRoot (xs : Array UInt64) (x : UInt64) : UInt64 := rootSum (pushAll x (three xs))

verified_compile compiled := [keep, single, count, keys, rootSum, pushAll, three, grown,
  grownRoot]

#print axioms compiled.bytes
#print axioms compiled.keep.implements
#print axioms compiled.pushAll.implements
#print axioms compiled.grown.implements

#guard count (three #[1, 2]) == 6
#guard keys (three #[1, 2]) == 6
#guard grown #[1, 2] 5 == 15
#guard grownRoot #[1, 2] 5 == 8

end Verified.Examples.ArrayTrees
