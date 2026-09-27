import Project.Beck.ExecutionExtendStep
import Project.ProofKit.BlockLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem rangeSearch_found {α : Type} (f : Nat → Option α) (width column : Nat) (value : α)
    (bound : column < width) (earlier : ∀ k < column, f k = none) (found : f column = some value) :
    (List.range width).findSome? f = some value := by
  have before : (List.range column).findSome? f = none := by
    simpa only [List.findSome?_eq_none_iff, List.mem_range] using earlier
  have through : (List.range (column + 1)).findSome? f = some value := by
    simp [List.range_succ, List.findSome?_append, before, found]
  have initial : List.range (column + 1) <+: List.range width := by
    simpa only [List.take_range, Nat.min_eq_left (by omega : column + 1 ≤ width)] using
      List.take_prefix (column + 1) (List.range width)
  exact initial.findSome?_eq_some through

def ExtendColumnOutput (original current : Heap) (store : Store Unit) (locals : List Value) (result : Option Basis) : Prop :=
  match result with
  | none => ExtendChoiceLocals locals false 0 0 0
  | some basis => ∃ rows columns, CandidateBasis original current store basis rows columns ∧
      ExtendChoiceLocals locals true rows.root columns.root basis.determinant

theorem CandidateBasis.original {original middle final : Heap} {initial current result : Store Unit}
    {basis : Basis} {rows columns : FreeNode} (owned : CandidateBasis middle final result basis rows columns)
    (preserved : original.Frame initial middle current) : CandidateBasis original final result basis rows columns := by
  exact ⟨owned.rowsOwned, owned.columnsOwned,
    fun lower upper region => owned.rowsFresh lower upper (preserved.protects lower upper region),
    fun lower upper region => owned.columnsFresh lower upper (preserved.protects lower upper region), owned.separated⟩

theorem ExtendSearchLocals.choice {locals : List Value} {row rows column width : Nat}
    (state : ExtendSearchLocals locals row rows column width) : ExtendChoiceLocals locals false 0 0 0 := by
  constructor <;> exact state.innerEmpty _ (by decide) (by decide)

def extendColumnMeasure (width : Nat) (_store : Store Unit) (frame : Locals) : Nat :=
  match (frame.locals[125]? : Option Value) with
  | some (.i64 column) => width - column.toNat
  | _ => 0

def extendColumnInv (initial : Store Unit) (heap : Heap) (width : Nat) (matrix : Array UInt64) (basis : Basis)
    (row : Nat) (params : List Value) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current column locals,
    current.At store ∧ heap.Frame initial current store ∧ column ≤ width ∧
    (∀ earlier < column, borderCandidate width matrix basis row earlier = none) ∧
    OutputBudget store current ((208 + determinantBytes (basis.rows.size + 1)) * (width - column) + remaining) pageLimit Project.Beck.«module» ∧
    ExtendSearchLocals locals row (matrix.size / width) column width ∧ frame = { params := params, locals := locals }

def extendColumnDone (initial : Store Unit) (heap : Heap) (width : Nat) (matrix : Array UInt64) (basis : Basis)
    (row : Nat) (params : List Value) (remaining pageLimit : Nat) : AssertionF Unit := fun store frame =>
  ∃ current locals, current.At store ∧ heap.Frame initial current store ∧
    OutputBudget store current remaining pageLimit Project.Beck.«module» ∧
    ExtendScanLocals locals row (matrix.size / width) width ∧
    ExtendColumnOutput heap current store locals ((List.range width).findSome? (borderCandidate width matrix basis row)) ∧
    frame = { params := params, locals := locals }

set_option maxRecDepth 4096 in
theorem extend_column_guard_shape : extendColumnBody =
    [.localGet 133, .localGet 134, .geUI64, .br_if 1] ++ extendColumnBody.drop 4 := rfl

#print axioms rangeSearch_found
#print axioms CandidateBasis.original

end Project.Beck.Execution
