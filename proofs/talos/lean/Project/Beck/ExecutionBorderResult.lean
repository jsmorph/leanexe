import Project.Beck.ExecutionBorderDeterminant
import Project.Beck.ExecutionFresh

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

structure CandidateBasis (original heap : Heap) (store : Store Unit) (basis : Basis)
    (rows columns : FreeNode) : Prop where
  rowsOwned : heap.OwnsWords store rows basis.rows
  columnsOwned : heap.OwnsWords store columns basis.columns
  rowsFresh : FreshFor original rows
  columnsFresh : FreshFor original columns
  separated : regionsDisjoint rows.region columns.region

def CandidateFrame (original heap : Heap) (store : Store Unit) (result : Option Basis) (frame : Locals) : Prop :=
  match result with
  | none => BorderResult frame 0 0 0
  | some basis => ∃ rows columns, CandidateBasis original heap store basis rows columns ∧ basis.determinant ≠ 0 ∧
      BorderResult frame rows.root columns.root basis.determinant

def CandidateOutput (original heap : Heap) (store : Store Unit) (result : Option Basis) (values : List Value) : Prop :=
  match result with
  | none => values = List.replicate 6 (.i64 0)
  | some basis => ∃ rows columns, CandidateBasis original heap store basis rows columns ∧
      values = basisValues basis rows.root rows.root columns.root columns.root ++ [.i64 1]

theorem BorderResult.zero {frame : Locals} {rows columns : UInt64} (h : BorderResult frame rows columns 0) :
    BorderResult frame 0 0 0 := by
  exact ⟨h.values, h.tag, by simpa using h.rowsOwner, by simpa using h.rowsPointer,
    by simpa using h.columnsOwner, by simpa using h.columnsPointer, h.determinant⟩

set_option maxRecDepth 2048 in
theorem borderReturn_exact (env : HostEnv Unit) (initial : Store Unit) (original heap : Heap)
    (frame : Locals) (result : Option Basis) (represented : CandidateFrame original heap initial result frame)
    (Q : Assertion Unit)
    (next : ∀ frame, CandidateOutput original heap initial result frame.values → Q (.Fallthrough initial frame)) :
    wp Project.Beck.«module» (func25.drop 22) Q initial frame env := by
  cases result with
  | none =>
    have h : BorderResult frame 0 0 0 := represented
    simp only [func25, List.drop, wp_simp, Frame.withValues_get, h.values, h.tag,
      h.rowsOwner, h.rowsPointer, h.columnsOwner, h.columnsPointer, h.determinant, reduceIte]
    exact next _ rfl
  | some basis =>
    obtain ⟨rows, columns, owned, nonzero, h⟩ := represented
    simp only [func25, List.drop, wp_simp, Frame.withValues_get, h.values, h.tag,
      h.rowsOwner, h.rowsPointer, h.columnsOwner, h.columnsPointer, h.determinant, nonzero, reduceIte]
    exact next _ ⟨rows, columns, owned, rfl⟩

#print axioms borderReturn_exact

end Project.Beck.Execution
