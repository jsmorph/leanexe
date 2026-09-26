import Project.Beck.ExecutionDetBase
import Project.ProofKit.CheckedArrayGet
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Beck.Execution

open Wasm Project.ProofKit

def determinantRead : Wasm.Program :=
  [.localGet 3, .localSet 48, .localGet 5, .localSet 55, .constI64 0, .localSet 56] ++
    CheckedArrayGet.checkedGetCore 55 56 ++ [.localSet 53, .localGet 1, .localSet 54] ++
    CheckedNatMul.program 53 54 ++
    [.localSet 50, .localGet 7, .localSet 53, .localGet 22, .localSet 54] ++
    CheckedArrayGet.checkedGetCore 53 54 ++
    [.localSet 51, .localGet 50, .localGet 51, .addI64, .localTee 52, .localGet 50, .ltUI64,
      .iff 0 1 [.unreachable] [.localGet 52] [] [.i64], .localSet 49] ++
    CheckedArrayGet.checkedGetCore 48 49

def determinantLoop : Wasm.Program :=
  match (determinantOuter[37]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

theorem determinant_first_read : (determinantLoop.drop 8).take 45 = determinantRead := by rfl

theorem determinant_second_read : (determinantLoop.drop 72).take 45 = determinantRead := by rfl

abbrev DeterminantReadScratch := Fin 52 → Value

def determinantReadFrame (fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64)
    (index : Nat) (scratch : DeterminantReadScratch) (values : List Value) : Locals :=
  { params := determinantParams fuel width matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
    locals := [scratch 0, scratch 1, scratch 2, scratch 3, scratch 4, scratch 5, scratch 6, scratch 7,
      scratch 8, scratch 9, scratch 10, scratch 11, scratch 12, scratch 13, .i64 index.toUInt64, scratch 15,
      scratch 16, scratch 17, scratch 18, scratch 19, scratch 20, scratch 21, scratch 22, scratch 23,
      scratch 24, scratch 25, scratch 26, scratch 27, scratch 28, scratch 29, scratch 30, scratch 31,
      scratch 32, scratch 33, scratch 34, scratch 35, scratch 36, scratch 37, scratch 38, scratch 39,
      scratch 40, scratch 41, scratch 42, scratch 43, scratch 44, scratch 45, scratch 46, scratch 47,
      scratch 48, scratch 49, scratch 50, scratch 51]
    values := values }

def determinantReadScratch (matrixPointer rowPointer columnPointer row column : UInt64)
    (width index : Nat) (scratch : DeterminantReadScratch) : DeterminantReadScratch := fun k =>
  match k.val with
  | 40 => .i64 matrixPointer
  | 41 | 44 => .i64 (row.toNat * width + column.toNat).toUInt64
  | 42 => .i64 (row.toNat * width).toUInt64
  | 43 => .i64 column
  | 45 => .i64 columnPointer
  | 46 => .i64 index.toUInt64
  | 47 => .i64 rowPointer
  | 48 => .i64 0
  | _ => scratch k

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
theorem determinantRead_exact (env : HostEnv Unit) (initial : Store Unit)
    (fuel matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer : UInt64)
    (width index : Nat) (matrix rows columns : Array UInt64)
    (scratch : DeterminantReadScratch) (values : List Value)
    (matrixAt : UInt64Array.At initial matrixPointer matrix)
    (rowsAt : UInt64Array.At initial rowPointer rows)
    (columnsAt : UInt64Array.At initial columnPointer columns)
    (nonempty : 0 < rows.size) (inside : index < columns.size)
    (widthFit : width < UInt64.size)
    (addressBound : rows[0].toNat * width + columns[index].toNat < matrix.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp Project.Beck.«module» rest Q initial
      (determinantReadFrame fuel width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
        index (determinantReadScratch matrixPointer rowPointer columnPointer rows[0] columns[index] width index scratch)
        (.i64 matrix[rows[0].toNat * width + columns[index].toNat] :: values)) env) :
    wp Project.Beck.«module» (determinantRead ++ rest) Q initial
      (determinantReadFrame fuel width.toUInt64 matrixOwner matrixPointer rowOwner rowPointer columnOwner columnPointer
        index scratch values) env := by
  have addressFit := lt_trans addressBound matrixAt.size_lt
  have productFit : rows[0].toNat * width < UInt64.size := by omega
  have mulFit : rows[0].toNat * (UInt64.ofNat width).toNat < UInt64.size := by
    rw [UInt64.toNat_ofNat_of_lt' widthFit]
    exact productFit
  have productWord : rows[0] * UInt64.ofNat width = UInt64.ofNat (rows[0].toNat * width) := by
    rw [UInt64.ofNat_mul, UInt64.ofNat_toNat]
  have columnWord : UInt64.ofNat columns[index].toNat = columns[index] := UInt64.ofNat_toNat
  have addressWord : UInt64.ofNat (rows[0].toNat * width) + columns[index] =
      UInt64.ofNat (rows[0].toNat * width + columns[index].toNat) := by
    rw [UInt64.ofNat_add, columnWord]
  have guard : ¬UInt64.ofNat (rows[0].toNat * width) + columns[index] < UInt64.ofNat (rows[0].toNat * width) := by
    have h := CheckedNatAdd.guard_of_fits (rows[0].toNat * width) columns[index].toNat addressFit
    simpa only [columnWord] using h
  simp only [determinantRead, List.append_assoc, List.cons_append, List.nil_append,
    determinantReadFrame, determinantParams]
  repeat' (first
    | (refine CheckedArrayGet.checkedGetCore_spec 55 56 Project.Beck.«module» env initial _ rowPointer
        rows 0 values rfl rfl rfl rowsAt nonempty _ _ ?_)
    | (refine CheckedNatMul.program_spec 53 54 Project.Beck.«module» env initial _ rows[0]
        (UInt64.ofNat width) values rfl rfl rfl mulFit _ _ ?_)
    | (refine CheckedArrayGet.checkedGetCore_spec 53 54 Project.Beck.«module» env initial _ columnPointer
        columns index values rfl rfl rfl columnsAt inside _ _ ?_)
    | (refine CheckedArrayGet.checkedGetCore_spec 48 49 Project.Beck.«module» env initial _ matrixPointer
        matrix (rows[0].toNat * width + columns[index].toNat) values rfl
        (by simp only [Locals.get, List.length, List.getElem?_cons_zero,
          List.getElem?_cons_succ, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub,
          reduceIte, productWord, addressWord]) rfl matrixAt addressBound _ _ ?_)
    | wp_fixed_frame_step
    | ((first | rw [wp_addI64_cons] | rw [wp_localTee_cons] | rw [wp_ltUI64_cons] | rw [wp_nil]) <;>
        simp only [Locals.set?, List.length, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
          List.take, List.drop, List.append_nil, Nat.toUInt64, productWord, guard, reduceIte])
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
  simpa only [Fin.coe_ofNat_eq_mod, Nat.reduceMod, determinantReadFrame, determinantParams, determinantReadScratch,
    Nat.reduceEqDiff, reduceIte, productWord, addressWord, List.take, List.drop,
    List.append_nil] using next

#print axioms determinantRead_exact

end Project.Beck.Execution
