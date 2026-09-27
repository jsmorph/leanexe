import Project.Beck.ExecutionExtendOuterLoop

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def extendEntryLocals (locals : List Value) (width size : Nat) (pointer : UInt64) : List Value :=
  let l := (((locals.set 122 (.i64 0)).set 127 (.i64 pointer)).set 125 (.i64 size.toUInt64)).set 126 (.i64 width.toUInt64)
  let l := (((l.set 123 (.i64 (size / width).toUInt64)).set 124 (.i64 1)).set 0 (.i64 0)).set 95 (.i64 0)
  let l := (((l.set 1 (.i64 0)).set 2 (.i64 0)).set 97 (.i64 0)).set 3 (.i64 0)
  ((l.set 4 (.i64 0)).set 5 (.i64 0)).set 6 (.i64 0)

theorem extendEntry_state (locals : List Value) (size : locals.length = 158) (width count : Nat) (pointer : UInt64) :
    ExtendOuterLocals (extendEntryLocals locals width count pointer) 0 (count / width) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [extendEntryLocals, size]
  · intro k bound
    interval_cases k <;> simp [extendEntryLocals, size]
  all_goals simp [extendEntryLocals, size]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem extendEntry_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (width : Nat) (matrix : Array UInt64) (matrixOwner matrixPointer : UInt64) (basis : Basis)
    (rowOwner rowPointer columnOwner columnPointer : UInt64)
    (localsSize : locals.length = 158) (widthBound : width ≤ 6)
    (represented : UInt64Array.At initial matrixPointer matrix) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer
        locals := extendEntryLocals locals width matrix.size matrixPointer })) :
    wp Project.Beck.«module» (func26.take 35) Q initial
      { params := extendParams width matrixOwner matrixPointer basis rowOwner rowPointer columnOwner columnPointer, locals := locals } env := by
  have widthFit : width < UInt64.size := by change width < 18446744073709551616; omega
  have wordZero : width.toUInt64 = 0 ↔ width = 0 := by
    rw [← UInt64.toNat_inj, UInt64.toNat_ofNat_of_lt' widthFit, UInt64.toNat_zero]
  have quotient : UInt64.ofNat matrix.size / UInt64.ofNat width = UInt64.ofNat (matrix.size / width) :=
    (UInt64.ofNat_div represented.size_lt widthFit).symm
  have lengthRead : initial.mem.read64 (UInt32.ofNat (matrixPointer.toNat % 2 ^ 32)) = UInt64.ofNat matrix.size := by
    simp only [Nat.reducePow]
    rw [represented.pointerAddress_eq]
    exact represented.lengthRead
  have lengthBound : (UInt32.ofNat (matrixPointer.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]
    rw [represented.pointerAddress_eq]
    exact represented.lengthBound
  by_cases zero : width.toUInt64 = 0
  all_goals
    simp only [func26, List.take]
    repeat' first
      | (wp_run [extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
          localsSize, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, List.append_nil, zero,
          lengthRead, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, Nat.not_lt.mpr lengthBound,
          show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp only [zero, show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  · simpa only [extendEntryLocals, extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append,
      List.nil_append, wordZero.mp zero, Nat.div_zero, Nat.toUInt64, show UInt64.ofNat 0 = 0 by decide] using next
  · simpa only [extendEntryLocals, extendParams, basisValues, List.reverse_cons, List.reverse_nil, List.cons_append,
      List.nil_append, Nat.toUInt64, quotient] using next

#print axioms extendEntry_exact

end Project.Beck.Execution
