import Verified.Reflect.Command

/-! A recursive type whose records hold a byte buffer beside a word and two children.  A record
holds its word and child slots in the order of the fields and then its buffer's root and length,
as the `Encode` instance states.  A construction moves a buffer into a record, a borrowed buffer
argument as a copy, and an empty buffer with root 0.  A match binds the buffer as a variable, an
owned match moves it out of the record and releases it when the branch does not use it, and a
copy of a borrowed tree copies the buffer of each record. -/

namespace Verified.Examples.BufferTrees

open LeanExe.Pipeline

/-- Names in a tree: nothing, or an entry with a key and a name between two subtrees. -/
inductive Names where
  | empty
  | entry (left : Names) (key : UInt64) (name : LeanExe.Bytes) (right : Names)

/-- `Names` as records: `empty` is the null pointer, and an entry a record of its left child, its
key, and its right child, followed by its name's root and length. -/
def Names.encode : Names → Node
  | .empty => .null
  | .entry l k n r =>
    .record [.child l.encode, .word k, .child r.encode, .bytes n, .word (UInt64.ofNat n.data.size)]

instance : Encode Names := ⟨Names.encode⟩

verified_recursive_type Names

def keep (t : Names) : Names := t

def single (k : UInt64) (n : LeanExe.Bytes) : Names := .entry .empty k n .empty

/-- The number of name bytes in the tree. -/
def total : Names → UInt64
  | .empty => 0
  | .entry l _ n r => total l + n.size + total r

/-- The sum of the keys, whose owned matches release the names. -/
def keys : Names → UInt64
  | .empty => 0
  | .entry l k _ r => keys l + k + keys r

/-- The first byte of the root's name. -/
def rootByte : Names → UInt64
  | .empty => 0
  | .entry _ _ n _ => n.get 0

/-- Three entries of the name `n`, each holding its own copy. -/
def three (n : LeanExe.Bytes) : Names := .entry (single 1 n) 2 n (single 3 n)

/-- The name bytes and keys of `three n`, the bytes counted on a copy of the tree. -/
def counted (n : LeanExe.Bytes) : UInt64 :=
  let t := three n
  total (keep t) + keys t

/-- The first byte of the root's name of `three n`. -/
def firstByte (n : LeanExe.Bytes) : UInt64 := rootByte (three n)

/-- An entry whose name is the empty buffer. -/
def unnamed (k : UInt64) : UInt64 := keys (single k LeanExe.Bytes.empty)

verified_compile compiled := [keep, single, total, keys, rootByte, three, counted, firstByte,
  unnamed]

#print axioms compiled.bytes
#print axioms compiled.keep.implements
#print axioms compiled.three.implements
#print axioms compiled.counted.implements

#guard counted bytes![1, 2] == 12
#guard firstByte bytes![9, 8] == 9
#guard unnamed 4 == 4

end Verified.Examples.BufferTrees
