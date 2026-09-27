import Project.Beck.ExecutionBorderCandidate
import Project.Beck.Basis

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem extend_candidate_input {width : Nat} {matrix : Array UInt64} {basis : Basis}
    (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size < 6)
    (row column : Nat) (rowBound : row < matrix.size / width) (columnBound : column < width) :
    DeterminantInput (basis.rows.size + 1) width matrix
      (basis.rows.push row.toUInt64) (basis.columns.push column.toUInt64) := by
  refine ⟨by omega, widthBound, matrixBound, by simp, by simp [wellFormed.square], ?_⟩
  intro r memberR c memberC
  have hr : r.toNat < matrix.size / width := by
    rcases Array.mem_push.mp memberR with old | rfl
    · exact wellFormed.rows.bound r old
    · exact (Nat.mod_le _ _).trans_lt rowBound
  have hc : c.toNat < width := by
    rcases Array.mem_push.mp memberC with old | rfl
    · exact wellFormed.columns.bound c old
    · exact (Nat.mod_le _ _).trans_lt columnBound
  have product := (Nat.mul_le_mul_right width (show r.toNat + 1 ≤ matrix.size / width by omega)).trans
    (Nat.div_mul_le_self matrix.size width)
  rw [Nat.add_mul, Nat.one_mul] at product
  omega

def extendParams (width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) : List Value :=
  [.i64 width.toUInt64, .i64 matrixOwner, .i64 matrixPointer] ++
    (basisValues basis rowOwner rowPointer columnOwner columnPointer).reverse

def extendBody : Wasm.Program := match (func26[35]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def extendColumnBody : Wasm.Program := match (extendBody[30]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem extend_column_call_shape : extendColumnBody[36]? = some (.call 25) := rfl

structure ExtendScanLocals (locals : List Value) (row rows width : Nat) : Prop where
  size : locals.length = 158
  outerEmpty : ∀ k ≤ 6, locals[k]? = some (.i64 0)
  currentRow : locals[7]? = some (.i64 row.toUInt64)
  rowIndex : locals[122]? = some (.i64 row.toUInt64)
  rowLimit : locals[123]? = some (.i64 rows.toUInt64)
  rowStep : locals[124]? = some (.i64 1)
  columnLimit : locals[126]? = some (.i64 width.toUInt64)
  columnStep : locals[127]? = some (.i64 1)
  oldRows : locals[137]? = some (.i64 0)
  oldColumns : locals[139]? = some (.i64 0)

structure ExtendSearchLocals (locals : List Value) (row rows column width : Nat)
    extends ExtendScanLocals locals row rows width : Prop where
  innerEmpty : ∀ k, 8 ≤ k → k ≤ 14 → locals[k]? = some (.i64 0)
  columnIndex : locals[125]? = some (.i64 column.toUInt64)

#print axioms extend_candidate_input

end Project.Beck.Execution
