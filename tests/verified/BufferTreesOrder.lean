import Verified.Reflect.Command

/-! `verified_recursive_type` rejects an `Encode` instance that places a buffer's root without its
length slot after it, and the error names the field.  The record layout of the verified compiler
holds a buffer as its root followed by a word slot that holds its length. -/

namespace Verified.Tests.BufferTreesOrder

open LeanExe.Pipeline

inductive Named where
  | leaf
  | node (left : Named) (key : UInt64) (name : LeanExe.Bytes)

def Named.encode : Named → Node
  | .leaf => .null
  | .node l k n => .record [.child l.encode, .word k, .bytes n]

instance : Encode Named := ⟨Named.encode⟩

/--
error: verified_recursive_type: the `Encode` instance of Verified.Tests.BufferTreesOrder.Named places the buffer field `name` of Verified.Tests.BufferTreesOrder.Named.node without its length slot after it; a record holds its word and child slots first and then its array and buffer slots, each group in the order of the fields, and a buffer's length slot after its root
-/
#guard_msgs in
verified_recursive_type Named

end Verified.Tests.BufferTreesOrder
