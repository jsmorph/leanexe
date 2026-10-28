import LeanExe.Pipeline.Implements

/-! The `records-u64` form of `build/tools/leanexe-wasmtime-host` for a value of a recursive
type: `.` for null, and for a record its width, its mask, and its slots in preorder, separated
by commas, where a child slot is written as a tree.  Native Lean computes the expected text from
the value's `Encode` instance, so a case compares the records that a module returns with the
layout of the instance.  An array or a buffer slot has no `records-u64` form: it is written as
`array` or `bytes`, which the host rejects. -/

namespace TestSupport.Host

open LeanExe.Pipeline

mutual
def nodeRecords : Node → String
  | .null => "."
  | .record slots => s!"{slots.length},{maskOf slots}{slotsRecords slots}"

def slotsRecords : List Slot → String
  | [] => ""
  | .word w :: rest => s!",{w}{slotsRecords rest}"
  | .child n :: rest => s!",{nodeRecords n}{slotsRecords rest}"
  | .array _ :: rest => s!",array{slotsRecords rest}"
  | .bytes _ :: rest => s!",bytes{slotsRecords rest}"
end

/-- The `records-u64` form of `x`. -/
def records [Encode α] (x : α) : String := nodeRecords (Encode.encode x)

/-- The `records-u64` argument of `x`. -/
def recordsArg [Encode α] (x : α) : String := s!"records-u64:{records x}"

end TestSupport.Host
