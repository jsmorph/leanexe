import Project.Beck.ExecutionDirectionSearch

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem direction_replacement_input {width : Nat} {matrix : Array UInt64} {basis : Basis}
    (wellFormed : Project.Beck.Basis.WellFormed width matrix basis)
    (widthBound : width ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size ≤ 6)
    (free index : Nat) (freeBound : free < width) :
    DeterminantInput basis.rows.size width matrix basis.rows (basis.columns.set! index free.toUInt64) := by
  refine ⟨rankBound, widthBound, matrixBound, rfl, by simp [wellFormed.square], ?_⟩
  intro row memberRow column memberColumn
  have rowBound := wellFormed.rows.bound row memberRow
  have columnBound : column.toNat < width := by
    rcases Array.mem_or_eq_of_mem_setIfInBounds memberColumn with old | rfl
    · exact wellFormed.columns.bound column old
    · exact (Nat.mod_le _ _).trans_lt freeBound
  have product := (Nat.mul_le_mul_right width (show row.toNat + 1 ≤ matrix.size / width by omega)).trans
    (Nat.div_mul_le_self matrix.size width)
  rw [Nat.add_mul, Nat.one_mul] at product
  omega

def directionDetLocals (locals : List Value) (order width : Nat) (matrix ro rp columns : UInt64) : List Value :=
  let l := (((locals.set 62 (.i64 columns)).set 63 (.i64 columns)).set 92 (.i64 rp)).set 64 (.i64 order.toUInt64)
  let l := (((l.set 65 (.i64 width.toUInt64)).set 66 (.i64 matrix)).set 67 (.i64 matrix)).set 68 (.i64 ro)
  ((l.set 69 (.i64 rp)).set 70 (.i64 columns)).set 71 (.i64 columns)

set_option maxRecDepth 4096 in
theorem directionDetPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (basis : Basis)
    (inputOwner inputPointer pointOwner pointPointer matrix sro srp sco scp ro rp co cp columns : UInt64)
    (state : DirectionSearchLocals locals matrix sro srp sco scp basis ro rp co cp)
    (rowsAt : UInt64Array.At initial rp basis.rows) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := directionDetLocals locals basis.rows.size input.jobs matrix ro rp columns
        values := (determinantParams basis.rows.size.toUInt64 input.jobs.toUInt64 matrix matrix ro rp columns columns).reverse })) :
    wp Project.Beck.«module» ((directionBody.drop 26).take 31) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals, values := [.i64 columns] } env := by
  have lengthRead : initial.mem.read64 (UInt32.ofNat (rp.toNat % 2 ^ 32)) = UInt64.ofNat basis.rows.size := by
    simp only [Nat.reducePow]; rw [rowsAt.pointerAddress_eq]; exact rowsAt.lengthRead
  have lengthBound : (UInt32.ofNat (rp.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [rowsAt.pointerAddress_eq]; exact rowsAt.lengthBound
  simp only [directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    state.size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, state.rowOwner, state.rowPointer, state.matrixOwner, state.matrixPointer,
    lengthRead, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, Nat.not_lt.mpr lengthBound, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem direction_det_shape : (directionBody.drop 26).take 32 = (directionBody.drop 26).take 31 ++ [.call 24] := rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem directionDeterminant_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (basis : Basis) (matrix : Array UInt64)
    (inputOwner inputPointer pointOwner pointPointer matrixPointer sro srp sco scp ro rp co cp columns : UInt64)
    (free index remaining pageLimit : Nat)
    (state : DirectionSearchLocals locals matrixPointer sro srp sco scp basis ro rp co cp)
    (valid : heap.At initial) (wellFormed : Project.Beck.Basis.WellFormed input.jobs matrix basis)
    (widthBound : input.jobs ≤ 6) (matrixBound : matrix.size ≤ 56) (rankBound : basis.rows.size ≤ 6) (freeBound : free < input.jobs)
    (matrixAt : UInt64Array.At initial matrixPointer matrix) (rowsAt : UInt64Array.At initial rp basis.rows)
    (columnsAt : UInt64Array.At initial columns (basis.columns.set! index free.toUInt64))
    (matrixProtected : heap.Protects matrixPointer.toNat (matrixPointer.toNat + 8 * (matrix.size + 1)))
    (rowsProtected : heap.Protects rp.toNat (rp.toNat + 8 * (basis.rows.size + 1)))
    (columnsProtected : heap.Protects columns.toNat (columns.toNat + 8 * ((basis.columns.set! index free.toUInt64).size + 1)))
    (budget : OutputBudget initial heap (determinantBytes basis.rows.size + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap, finalHeap.At final → heap.Frame initial finalHeap final →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
          locals := directionDetLocals locals basis.rows.size input.jobs matrixPointer ro rp columns
          values := [.i64 (determinant basis.rows.size input.jobs matrix basis.rows (basis.columns.set! index free.toUInt64))] })) :
    wp Project.Beck.«module» ((directionBody.drop 26).take 32) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals, values := [.i64 columns] } env := by
  rw [direction_det_shape]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame =
    { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
      locals := directionDetLocals locals basis.rows.size input.jobs matrixPointer ro rp columns,
      values := (determinantParams basis.rows.size.toUInt64 input.jobs.toUInt64 matrixPointer matrixPointer ro rp columns columns).reverse })
  · exact directionDetPrepare_exact env initial locals input point basis inputOwner inputPointer pointOwner pointPointer matrixPointer
      sro srp sco scp ro rp co cp columns state rowsAt _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine wp_call_tw (determinant_exact env basis.rows.size initial heap input.jobs matrix basis.rows (basis.columns.set! index free.toUInt64)
    matrixPointer matrixPointer ro rp columns columns remaining pageLimit valid
    (direction_replacement_input wellFormed widthBound matrixBound rankBound free index freeBound)
    matrixAt rowsAt columnsAt matrixProtected rowsProtected columnsProtected budget) ?_
  rintro final values ⟨rfl, finalHeap, finalValid, preserved, finalBudget⟩
  rw [wp_nil]
  exact next final finalHeap finalValid preserved finalBudget

#print axioms direction_replacement_input
#print axioms directionDeterminant_exact

end Project.Beck.Execution
