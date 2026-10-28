import LeanExe.Pipeline.Implements

/-!
A `LeanExe.Bytes` value appears to a compiled function as two words, a root and a length.  An
empty buffer has root 0 or the root of an object without bytes, and a nonempty buffer is an object
that `Heap.Buffer` describes.  These definitions give `LeanExe.Bytes` parameters and results their
meaning in `Implements`, as `Heap.Owned` and `Heap.Borrowed` give arrays theirs.
-/

namespace LeanExe.Pipeline.Bytes

open Wasm

/-- The buffer `bytes` at the root `root` with the length `length`: the length is the number of
bytes, and the root is 0 with no bytes or the root of a buffer object that holds them. -/
structure Rep (heap : Heap) (store : Store Unit) (root length : UInt64)
    (bytes : LeanExe.Bytes) : Prop where
  length_eq : length.toNat = bytes.data.size
  buffer : (root = 0 ∧ bytes.data.size = 0) ∨ Heap.Buffer heap store root bytes

/-- The root among the words `values` of a buffer, when it is not 0. -/
def roots : List Value → List UInt64
  | [.i64 root, .i64 _] => if root = 0 then [] else [root]
  | _ => []

/-- The words `values` are the root and the length of the buffer `bytes`. -/
def represented (heap : Heap) (store : Store Unit) (values : List Value)
    (bytes : LeanExe.Bytes) : Prop :=
  ∃ root length, values = [.i64 root, .i64 length] ∧ Rep heap store root length bytes

end LeanExe.Pipeline.Bytes

namespace LeanExe.Pipeline

open Wasm

/-- A buffer is its root and its length, in either mode.  The call reads the block of an object
at a nonzero root, and a result's object at a nonzero root is owned. -/
instance : Represent LeanExe.Bytes where
  width _ := 2
  borrowed := Bytes.represented
  owned := Bytes.represented
  blocks store values _ := (Bytes.roots values).map (block store)
  reads store values _ := (Bytes.roots values).map (block store)
  moves _ _ _ := []

/-- A buffer that the caller hands over: the call receives its object as owned, reads nothing
else of it, and consumes the object at a nonzero root. -/
instance : Represent (Moved LeanExe.Bytes) where
  width _ := 2
  borrowed heap store values bytes := Bytes.represented heap store values bytes.val
  owned heap store values bytes := Bytes.represented heap store values bytes.val
  blocks store values _ := (Bytes.roots values).map (block store)
  reads _ _ _ := []
  moves _ values _ := Bytes.roots values

end LeanExe.Pipeline
