import Verified.Reflect.Command
import Library.Trees.WordTree.Reflected

/-! Sums whose constructors hold heap values: packed bytes, arrays, and recursive types.  Each
sum's `Flat` instance places a constructor's fields in the tuple and fills the other components
with the instance's values for inactive fields: `Bytes.empty`, which allocates nothing, `#[]`,
which allocates an empty array, and a null tree.  A match destructures the tuple once and
releases the owned components that its branch does not use. -/

namespace Verified.Examples.HeapSums

open LeanExe.Pipeline Library.Trees.WordTree

/-- A message: packed text, a scaled array of words, a weighted tree of keys, or nothing. -/
inductive Item where
  | text (body : LeanExe.Bytes)
  | words (xs : Array UInt64) (scale : UInt64)
  | keys (tree : KeyTree) (weight : Float)
  | none

instance : Flat Item (UInt64 × LeanExe.Bytes × Array UInt64 × UInt64 × KeyTree × Float) := ⟨fun
  | .text body => (0, body, #[], 0, .leaf, 0)
  | .words xs scale => (1, .empty, xs, scale, .leaf, 0)
  | .keys tree weight => (2, .empty, #[], 0, tree, weight)
  | .none => (3, .empty, #[], 0, .leaf, 0)⟩

/-- The item that `k` selects, holding the argument of its constructor. -/
def make (k : UInt64) (body : LeanExe.Bytes) (xs : Array UInt64) (tree : KeyTree) : Item :=
  if k = 0 then .text body
  else if k = 1 then .words xs k
  else if k = 2 then .keys tree 1.5
  else .none

/-- The key at the root of a tree, or 0. -/
def rootKey (t : KeyTree) : UInt64 :=
  match t with
  | .leaf => 0
  | .node _ k _ => k

/-- A size of the item, read without taking it apart. -/
def measure (i : Item) : UInt64 :=
  match i with
  | .text body => body.size
  | .words xs scale => xs.size.toUInt64 * scale
  | .keys tree weight => rootKey tree + weight.toUInt64
  | .none => 0

/-- The text of the item, or no bytes. -/
def textOf (i : Item) : LeanExe.Bytes :=
  match i with
  | .text b => b
  | _ => LeanExe.Bytes.empty

/-- The item with its scale appended to its words, and any other item unchanged. -/
def rescale (i : Item) : Item :=
  match i with
  | .words xs scale => .words (xs.push scale) (scale + 1)
  | other => other

/-- The words of the item that `k` selects, which the match takes from an owned value. -/
def extract (k : UInt64) (b : LeanExe.Bytes) (xs : Array UInt64) (tree : KeyTree) :
    Array UInt64 :=
  match make k b xs tree with
  | .words ys _ => ys
  | _ => #[]

/-- The size of the item that `k` selects, which is released after the read. -/
def consume (k : UInt64) (b : LeanExe.Bytes) (xs : Array UInt64) (tree : KeyTree) : UInt64 :=
  measure (make k b xs tree)

/-- The item with its size added to `n`. -/
def tally (i : Item) (n : UInt64) : Item × UInt64 := (i, n + measure i)

/-- The item after `n` steps, each of which appends the step's index to the words of a words
item.  The alternative `other` names the matched state, so each step copies the state before the
match takes it apart. -/
def grow (n : UInt64) (i : Item) : Item :=
  LeanExe.loop n i fun j s =>
    match s with
    | .words xs scale => .words (xs.push j) scale
    | other => other

/-- `grow` with every other constructor rebuilt from its fields, which moves the fields and
allocates the empty array of a text, a tree, or an empty item again. -/
def regrow (n : UInt64) (i : Item) : Item :=
  LeanExe.loop n i fun j s =>
    match s with
    | .words xs scale => .words (xs.push j) scale
    | .text b => .text b
    | .keys tree weight => .keys tree weight
    | .none => .none

/-- The item with a text turned into its length as a word, words turned into their low bytes,
and the root key of a tree set to 7. -/
def convert (i : Item) : Item :=
  match i with
  | .text b => .words (LeanExe.build 1 fun _ => b.size) 1
  | .words xs _ => .text (LeanExe.Bytes.build xs.size.toUInt64 fun j => xs[j.toNat]!)
  | .keys tree weight => .keys (tree.setKey 7) (weight * 2)
  | .none => .none

/-- A list of words or a count. -/
inductive Cell where
  | chain (xs : List UInt64)
  | count (n : UInt64)

instance : Flat Cell (UInt64 × List UInt64 × UInt64) := ⟨fun
  | .chain xs => (0, xs, 0)
  | .count n => (1, [], n)⟩

def cellOf (k : UInt64) (xs : List UInt64) : Cell := if k = 0 then .chain xs else .count k

def cellTotal (c : Cell) : UInt64 :=
  match c with
  | .chain xs => xs.foldl (· + ·) 0
  | .count n => n

/-- The sum of the words, by recursion that is not a tail call. -/
def total : List UInt64 → UInt64
  | [] => 0
  | x :: xs => x + total xs

/-- The total of a cell, through a call of the guarded `total`. -/
def cellSize (c : Cell) : UInt64 :=
  match c with
  | .chain xs => total xs
  | .count n => n

verified_compile compiled := [rootKey, KeyTree.setKey, make, measure, textOf, rescale, extract,
  consume, tally, grow, regrow, convert, cellOf, cellTotal, total, cellSize]

#print axioms compiled.bytes
#print axioms compiled.make.implements
#print axioms compiled.extract.trapFree
#print axioms compiled.grow.bound_eq

#guard measure (make 0 bytes![1, 2, 3] #[7] .leaf) == 3
#guard measure (make 1 .empty #[1, 2, 3] .leaf) == 3
#guard measure (make 2 .empty #[] (.node .leaf 4 .leaf)) == 5
#guard measure (make 9 .empty #[] .leaf) == 0
#guard (textOf (make 0 bytes![9, 8] #[] .leaf)).data.toList == [9, 8]
#guard (textOf (make 1 bytes![9, 8] #[] .leaf)).size == 0
#guard extract 1 .empty #[4, 5] .leaf == #[4, 5]
#guard extract 0 .empty #[4, 5] .leaf == #[]
#guard consume 1 .empty #[4, 5] .leaf == 2
#guard (tally (make 1 .empty #[1] .leaf) 10).2 == 11
#guard measure (rescale (make 1 .empty #[1, 2] .leaf)) == 6
#guard measure (rescale (make 0 bytes![1] #[] .leaf)) == 1
#guard measure (grow 3 (make 1 .empty #[] .leaf)) == 3
#guard measure (grow 3 (make 0 bytes![1, 2] #[] .leaf)) == 2
#guard measure (regrow 3 (make 1 .empty #[] .leaf)) == 3
#guard measure (regrow 3 (make 0 bytes![1, 2] #[] .leaf)) == 2
#guard measure (convert (make 1 .empty #[1, 2, 300] .leaf)) == 3
#guard (textOf (convert (make 1 .empty #[1, 2, 300] .leaf))).data.toList == [1, 2, 44]
#guard measure (convert (make 0 bytes![1, 2] #[] .leaf)) == 1
#guard measure (convert (make 2 .empty #[] (.node .leaf 4 .leaf))) == 10
#guard cellTotal (cellOf 0 [1, 2, 3]) == 6
#guard cellTotal (cellOf 5 [1, 2, 3]) == 5
#guard cellSize (cellOf 0 [1, 2, 3]) == 6
#guard cellSize (cellOf 4 [1, 2, 3]) == 4

end Verified.Examples.HeapSums
