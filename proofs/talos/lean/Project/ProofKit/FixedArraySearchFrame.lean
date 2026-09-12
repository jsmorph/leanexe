import Project.ProofKit.Frame
import Project.Runtime.FreeList

namespace Project.ProofKit.FixedArraySearch
open Wasm

def frame (params saved tail : List Wasm.Value)
    (need previous current capacity next result : UInt64) : Locals :=
  { params := params
    locals := saved ++ ([.i64 need, .i64 previous, .i64 current,
      .i64 capacity, .i64 next, .i64 result] ++ tail)
    values := [] }

theorem frame_get (params saved tail : List Wasm.Value)
    (need previous current capacity next result : UInt64) (field : Nat) (hf : field < 6) :
    (frame params saved tail need previous current capacity next result).get
      (params.length + saved.length + field) =
      [.i64 need, .i64 previous, .i64 current, .i64 capacity, .i64 next, .i64 result][field]? := by
  interval_cases field <;>
    simp [frame, Locals.get, Nat.add_assoc]

theorem frame_set_capacity (params saved tail : List Wasm.Value)
    (need previous current capacity next result value : UInt64) :
    (frame params saved tail need previous current capacity next result).set?
      (params.length + saved.length + 3) (.i64 value) =
      some (frame params saved tail need previous current value next result) := by
  simp [frame, Locals.set?, Nat.add_assoc]

theorem frame_set_next (params saved tail : List Wasm.Value)
    (need previous current capacity next result value : UInt64) :
    (frame params saved tail need previous current capacity next result).set?
      (params.length + saved.length + 4) (.i64 value) =
      some (frame params saved tail need previous current capacity value result) := by
  simp [frame, Locals.set?, Nat.add_assoc]

theorem frame_set_previous (params saved tail : List Wasm.Value)
    (need previous current capacity next result value : UInt64) :
    (frame params saved tail need previous current capacity next result).set?
      (params.length + saved.length + 1) (.i64 value) =
      some (frame params saved tail need value current capacity next result) := by
  simp [frame, Locals.set?, Nat.add_assoc]

theorem frame_set_current (params saved tail : List Wasm.Value)
    (need previous current capacity next result value : UInt64) :
    (frame params saved tail need previous current capacity next result).set?
      (params.length + saved.length + 2) (.i64 value) =
      some (frame params saved tail need previous value capacity next result) := by
  simp [frame, Locals.set?, Nat.add_assoc]

#print axioms frame_get
#print axioms frame_set_capacity
#print axioms frame_set_next
#print axioms frame_set_previous
#print axioms frame_set_current

end Project.ProofKit.FixedArraySearch
