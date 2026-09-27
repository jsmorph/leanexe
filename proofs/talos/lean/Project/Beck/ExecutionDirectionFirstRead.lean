import Project.Beck.ExecutionDirectionSet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionFirstLocals (locals : List Value) (ptr value : UInt64) (free size : Nat) : List Value :=
  let l := (((locals.set 49 (.i64 ptr)).set 50 (.i64 free.toUInt64)).set 89 (.i64 ptr)).set 90 (.i64 free.toUInt64)
  (l.set 95 (.i64 value)).set 91 (.i64 size.toUInt64)

set_option maxRecDepth 4096 in
theorem directionFirstRead_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (ptr value : UInt64) (words : Array UInt64) (free : Nat)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (pointerRead : locals[90]? = some (.i64 ptr)) (freeRead : locals[46]? = some (.i64 free.toUInt64))
    (valueRead : locals[33]? = some (.i64 value)) (represented : UInt64Array.At initial ptr words)
    (inside : free < words.size) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := params, locals := directionFirstLocals locals ptr value free words.size, values := [.i32 1] })) :
    wp Project.Beck.«module» ((directionEligible.drop 48).take 17) Q initial { params := params, locals := locals } env := by
  have lengthRead : initial.mem.read64 (UInt32.ofNat (ptr.toNat % 2 ^ 32)) = UInt64.ofNat words.size := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthRead
  have lengthBound : (UInt32.ofNat (ptr.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthBound
  have wordInside : free.toUInt64 < words.size.toUInt64 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (inside.trans represented.size_lt), UInt64.toNat_ofNat_of_lt' represented.size_lt]
    exact inside
  simp only [directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, pointerRead, freeRead, valueRead,
    lengthRead, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, Nat.not_lt.mpr lengthBound, wordInside, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem directionFirstCount_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (length : Nat) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (lengthRead : locals[91]? = some (.i64 length.toUInt64)) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := locals.set 92 (.i64 length.toUInt64) })) :
    wp Project.Beck.«module» (directionSetFirst.take 4) Q initial { params := params, locals := locals } env := by
  simp only [directionSetFirst, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take]
  wp_run [paramsSize, localsSize, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, lengthRead, UInt64.mul_one, reduceIte]
  exact next

#print axioms directionFirstRead_exact
#print axioms directionFirstCount_exact

end Project.Beck.Execution
