import Project.Beck.ExecutionFindBasisPrepare

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def findBasisReadLocals (locals : List Value) (basis : Basis) (rowOwner rowPointer columnOwner columnPointer oldRowPointer : UInt64) : List Value :=
  let l := (((locals.set 21 (.i64 basis.determinant)).set 20 (.i64 columnPointer)).set 19 (.i64 columnOwner)).set 18 (.i64 rowPointer)
  let l := (((l.set 17 (.i64 rowOwner)).set 22 (.i64 rowOwner)).set 23 (.i64 rowPointer)).set 24 (.i64 columnOwner)
  let l := ((l.set 25 (.i64 columnPointer)).set 26 (.i64 basis.determinant)).set 46 (.i64 rowPointer)
  l.set 46 (.i64 oldRowPointer)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem findBasisRead_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (fuel width : Nat) (matrixOwner matrixPointer : UInt64) (basis nextBasis : Basis)
    (rowOwner rowPointer columnOwner columnPointer nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer : UInt64)
    (size : locals.length = 47)
    (oldRows : UInt64Array.At initial rowPointer basis.rows) (newRows : UInt64Array.At initial nextRowPointer nextBasis.rows)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := findBasisReadLocals locals nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer rowPointer
        values := [.i32 (if nextBasis.rows.size = basis.rows.size then 1 else 0)] })) :
    wp Project.Beck.«module» ((findBasisBody.drop 32).take 33) Q initial
      { params := findBasisParams fuel width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := locals
        values := basisValues nextBasis nextRowOwner nextRowPointer nextColumnOwner nextColumnPointer } env := by
  have sameSize : nextBasis.rows.size.toUInt64 = basis.rows.size.toUInt64 ↔ nextBasis.rows.size = basis.rows.size := by
    rw [← UInt64.toNat_inj, UInt64.toNat_ofNat_of_lt' newRows.size_lt, UInt64.toNat_ofNat_of_lt' oldRows.size_lt]
  have oldRead : initial.mem.read64 (UInt32.ofNat (rowPointer.toNat % 2 ^ 32)) = UInt64.ofNat basis.rows.size := by
    simp only [Nat.reducePow]; rw [oldRows.pointerAddress_eq]; exact oldRows.lengthRead
  have oldBound : (UInt32.ofNat (rowPointer.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [oldRows.pointerAddress_eq]; exact oldRows.lengthBound
  have newRead : initial.mem.read64 (UInt32.ofNat (nextRowPointer.toNat % 2 ^ 32)) = UInt64.ofNat nextBasis.rows.size := by
    simp only [Nat.reducePow]; rw [newRows.pointerAddress_eq]; exact newRows.lengthRead
  have newBound : (UInt32.ofNat (nextRowPointer.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [newRows.pointerAddress_eq]; exact newRows.lengthBound
  by_cases same : nextBasis.rows.size.toUInt64 = basis.rows.size.toUInt64
  all_goals
    simp only [findBasisBody, func27, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
    repeat' first
      | (wp_run [findBasisParams, extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
          size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil, same,
          oldRead, newRead, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero,
          Nat.not_lt.mpr oldBound, Nat.not_lt.mpr newBound,
          show (1 : UInt64) ≠ 0 by decide, show (0 : UInt64) ≠ 1 by decide, show (1 : UInt32) ≠ 0 by decide,
          ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  · simpa only [findBasisReadLocals, findBasisParams, extendParams, basisValues, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append, sameSize.mp same, reduceIte] using next
  · simpa only [findBasisReadLocals, findBasisParams, extendParams, basisValues, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append, show nextBasis.rows.size ≠ basis.rows.size from mt sameSize.mpr same, reduceIte] using next

#print axioms findBasisRead_exact

end Project.Beck.Execution
