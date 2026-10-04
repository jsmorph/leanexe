import Project.IR.Record
import Project.IR.Function

/-! The copy function of a recursive type, which the compiler generates and the proofs name. -/

namespace Project.IR

/-- The depth at which an internal function traps at `unreachable`. -/
def recursionDepthLimit : UInt64 := 1000

/-- The copy function of a recursive type whose record has the slots `children`, `true` for a
child and `false` for a word, at function `index`.  Its parameters are the pointer and the depth.
It runs the depth guard, returns 0 for the null pointer, and for a record loads its slots, calls
itself at the depth plus one on each child in slot order, and returns a new record with the words
and the copies.  Local 2 holds the result. -/
def Func.copy (children : List Bool) (index : Nat) : Func :=
  let n := children.length
  let childSlots := (List.range n).filter fun i => children.getD i false
  let field (i : Nat) : Nat := 3 + i
  let copyLocal (j : Nat) : Nat := 3 + n + j
  let dst := 3 + n + childSlots.length
  let loads := (List.range n).map fun i =>
    Stmt.load .u64 (field i) (.bin .add (.get 0) (.const (UInt64.ofNat (8 * i))))
  let calls := childSlots.zipIdx.map fun (i, j) =>
    Stmt.call index [⟨.u64, .get (field i)⟩, ⟨.u64, .bin .add (.get 1) (.const 1)⟩]
      [copyLocal j]
  let values : List (Expr .u64) := (List.range n).map fun i =>
    match childSlots.idxOf? i with
    | some j => .get (copyLocal j)
    | none => .get (field i)
  let mask := UInt64.ofNat ((childSlots.map (2 ^ ·)).sum)
  let guard : Stmt := .ite (.ltU (.const (recursionDepthLimit - 1)) (.get 1)) .abort .skip
  let record := seqAll (loads ++ calls ++ [Stmt.record dst values mask, .assign 2 (.get dst)])
  { params := [.u64, .u64], vars := List.replicate (1 + n + childSlots.length + 1) .u64
    body := seqAll [guard, .ite (.eq (.get 0) (.const 0)) (.assign 2 (.const 0)) record]
    results := [⟨.u64, .get 2⟩] }

end Project.IR
