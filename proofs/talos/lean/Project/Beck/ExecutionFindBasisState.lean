import Project.Beck.ExecutionExtend

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def findBasisParams (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64) : List Value :=
  .i64 fuel.toUInt64 :: extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer

def findBasisBody : Wasm.Program := match (func27[8]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def findBasisContinue : Wasm.Program := match (findBasisBody[65]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

structure BasisReferences (heap : Heap) (store : Store Unit) (basis : Basis) (rows columns : UInt64) : Prop where
  rowsAt : UInt64Array.At store rows basis.rows
  columnsAt : UInt64Array.At store columns basis.columns
  rowsProtected : heap.Protects rows.toNat (rows.toNat + 8 * (basis.rows.size + 1))
  columnsProtected : heap.Protects columns.toNat (columns.toNat + 8 * (basis.columns.size + 1))

theorem BasisReferences.preserved {before after : Heap} {initial final : Store Unit}
    {basis : Basis} {rows columns : UInt64} (refs : BasisReferences before initial basis rows columns)
    (frame : before.Frame initial after final) : BasisReferences after final basis rows columns :=
  ⟨frame.words refs.rowsProtected refs.rowsAt, frame.words refs.columnsProtected refs.columnsAt,
    frame.protects _ _ refs.rowsProtected, frame.protects _ _ refs.columnsProtected⟩

theorem CandidateBasis.references {original heap : Heap} {store : Store Unit} {basis : Basis} {rows columns : FreeNode}
    (owned : CandidateBasis original heap store basis rows columns) : BasisReferences heap store basis rows.root columns.root :=
  ⟨owned.rowsOwned.buffer.values, owned.columnsOwned.buffer.values,
    ownedWords_protects owned.rowsOwned, ownedWords_protects owned.columnsOwned⟩

theorem CandidateBasis.preserved {original before after : Heap} {initial final : Store Unit}
    {basis : Basis} {rows columns : FreeNode} (owned : CandidateBasis original before initial basis rows columns)
    (frame : before.Frame initial after final) (valid : after.At final) : CandidateBasis original after final basis rows columns :=
  ⟨frame.ownsWords valid owned.rowsOwned, frame.ownsWords valid owned.columnsOwned,
    owned.rowsFresh, owned.columnsFresh, owned.separated⟩

def BasisOutput (original current : Heap) (store : Store Unit) (initialBasis : Basis)
    (initialValues : List Value) (basis : Basis) (values : List Value) : Prop :=
  (basis = initialBasis ∧ values = initialValues) ∨
    ∃ rows columns, CandidateBasis original current store basis rows columns ∧
      values = basisValues basis rows.root rows.root columns.root columns.root

theorem BasisOutput.preserved {original before after : Heap} {initial final : Store Unit}
    {initialBasis basis : Basis} {initialValues values : List Value}
    (output : BasisOutput original before initial initialBasis initialValues basis values)
    (frame : before.Frame initial after final) (valid : after.At final) :
    BasisOutput original after final initialBasis initialValues basis values := by
  rcases output with unchanged | ⟨rows, columns, owned, output⟩
  · exact Or.inl unchanged
  · exact Or.inr ⟨rows, columns, owned.preserved frame valid, output⟩

theorem findBasis_stable (fuel width : Nat) (matrix : Array UInt64) (basis : Basis)
    (stable : Project.Beck.Basis.extension width matrix basis = none) : findBasis fuel width matrix basis = basis := by
  cases fuel <;> simp [findBasis, Project.Beck.Basis.extend_eq, stable]

theorem findBasis_growing (fuel width : Nat) (matrix : Array UInt64) (basis next : Basis)
    (growing : Project.Beck.Basis.extension width matrix basis = some next) :
    findBasis (fuel + 1) width matrix basis = findBasis fuel width matrix next := by
  obtain ⟨row, _, column, _, candidate⟩ := Project.Beck.Basis.extension_some width matrix basis next growing
  have size := (Project.Beck.Basis.candidate_grows width matrix basis next row column candidate).1
  simp [findBasis, Project.Beck.Basis.extend_eq, growing, size]

def findBasisRoundBytes (width : Nat) (matrix : Array UInt64) : Nat := 200368 * width * (matrix.size / width)

theorem extend_bytes_bound {width : Nat} {matrix : Array UInt64} {basis : Basis}
    (rankBound : basis.rows.size < 6) :
    (208 + determinantBytes (basis.rows.size + 1)) * width * (matrix.size / width) ≤ findBasisRoundBytes width matrix := by
  have determinantBound := determinantBytes_bound (basis.rows.size + 1) (by omega)
  exact Nat.mul_le_mul_right (matrix.size / width) (Nat.mul_le_mul_right width (by omega))

#print axioms BasisOutput.preserved
#print axioms findBasis_growing
#print axioms extend_bytes_bound

end Project.Beck.Execution
