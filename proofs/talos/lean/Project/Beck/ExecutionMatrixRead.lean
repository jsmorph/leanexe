import Project.Beck.ExecutionMatrixFrame

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
theorem matrixRead_exact (env : HostEnv Unit) (initial : Store Unit) (input : Input) (point : Point)
    (inputOwner inputPointer pointOwner pointPointer : UInt64) (category index : Nat)
    (pointer initialOwner : UInt64) (words : Array UInt64) (saved : MatrixSaved) (tail : MatrixTail) (after : MatrixAfter)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (wordsAt : UInt64Array.At initial pointer words)
    (pointSize : input.jobs ≤ point.numerators.size)
    (inputSize : input.incidence.size = input.jobs * input.categories)
    (jobs : input.jobs ≤ 6) (categories : input.categories ≤ 8)
    (categoryBound : category < input.categories) (indexBound : index < input.jobs)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : let scratch := matrixEntryScratch inputPointer input.categories category index (frozen point index) tail
      wp Project.Beck.«module» rest Q initial
        (matrixPushFrame (matrixParams input point inputOwner inputPointer pointOwner pointPointer)
          (matrixReadSaved input point pointOwner pointPointer category index pointer saved)
          pointer words.size (tail 4) (tail 5) (matrixEntry input point category index) (tail 7) (tail 8)
          (scratch 9) (scratch 10) (scratch 11) (scratch 12) (scratch 13) (scratch 14)
          (matrixEntryAfter input initialOwner (frozen point index) after)) env) :
    wp Project.Beck.«module» ((matrixRowBody.drop 4).take 46 ++ rest) Q initial
      (matrixRowFrame input point inputOwner inputPointer pointOwner pointPointer category index pointer initialOwner saved tail after) env := by
  have indexFit : index < UInt64.size := by change index < 18446744073709551616; omega
  have categoryFit : input.categories < UInt64.size := by change input.categories < 18446744073709551616; omega
  have productFit : index * input.categories < UInt64.size := by change index * input.categories < 18446744073709551616; nlinarith
  have addressBound : index * input.categories + category < input.incidence.size := by rw [inputSize]; nlinarith
  have addressFit := lt_trans addressBound inputArray.size_lt
  have addressGuard := CheckedNatAdd.guard_of_fits (index * input.categories) category addressFit
  have productWord : UInt64.ofNat index * UInt64.ofNat input.categories = UInt64.ofNat (index * input.categories) :=
    (UInt64.ofNat_mul _ _).symm
  have addressWord : UInt64.ofNat (index * input.categories) + UInt64.ofNat category =
      UInt64.ofNat (index * input.categories + category) := (UInt64.ofNat_add _ _).symm
  have frozenCall := frozen_exact env initial point pointOwner pointPointer index pointArray (lt_of_lt_of_le indexBound pointSize)
  have mulFit : (UInt64.ofNat index).toNat * (UInt64.ofNat input.categories).toNat < UInt64.size := by
    rw [UInt64.toNat_ofNat_of_lt' indexFit, UInt64.toNat_ofNat_of_lt' categoryFit]
    exact productFit
  have headerBound : pointer.toUInt32.toNat + 8 ≤ initial.mem.pages * 65536 := by
    rw [wordsAt.pointerAddress_toNat]
    have := wordsAt.2.1
    omega
  have lengthWord : UInt64.ofNat words.size + 1 = UInt64.ofNat (words.size + 1) := (UInt64.ofNat_add _ _).symm
  cases frozenEq : frozen point index
  all_goals
    simp only [matrixRowBody, matrixSelected, matrixBody, func19, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.drop, List.take, List.cons_append, List.nil_append, matrixRowFrame, matrixParams, matrixPrefix, matrixTail,
      matrixSuffix, matrixRowSaved, matrixRowAfter, inputValues, pointValues, List.reverse_cons, List.reverse_nil,
      List.cons_append, List.nil_append, Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, reduceIte]
    repeat' (first
      | (refine wp_call_tw frozenCall ?_; rintro final values ⟨same, rfl⟩; subst final)
      | (refine CheckedNatMul.program_spec 86 87 Project.Beck.«module» env initial _
          (UInt64.ofNat index) (UInt64.ofNat input.categories) [] rfl rfl rfl mulFit _ _ ?_)
      | (refine CheckedArrayGet.checkedGetCore_spec 81 82 Project.Beck.«module» env initial _ inputPointer
          input.incidence (index * input.categories + category) [] rfl (by simp [Locals.get])
          rfl inputArray addressBound _ _ ?_)
      | wp_fixed_frame_step
      | ((first
          | rw [wp_eqI64_cons] | rw [wp_eqz_cons] | rw [wp_neI64_cons]
          | rw [wp_ltUI64_cons] | rw [wp_addI64_cons] | rw [wp_const_cons]
          | rw [wp_localTee_cons] | rw [wp_nil]) <;>
        simp only [Locals.set?, List.length, List.set, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT,
          List.take, List.drop, List.append_nil, List.cons_append, List.nil_append, Nat.toUInt64, boolWord, frozenEq,
          productWord, addressGuard, reduceIte])
      | (try simp only [wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]))
    wp_fixed_frame
    rw [show 2 ^ 32 = 4294967296 by decide, ← Memory.toUInt32_eq_ofNat]
    simp only [UInt32.toNat_zero, UInt32.add_zero, Nat.add_zero, Nat.not_lt.mpr headerBound, reduceIte, wordsAt.lengthRead]
    try wp_fixed_frame
    simpa only [matrixPushFrame, matrixParams, matrixReadSaved, matrixRowSaved, matrixPrefix, matrixSuffix,
      matrixEntryScratch, matrixEntryAfter, matrixRowAfter, matrixEntry, inputValues, pointValues,
      frozenEq, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod, Nat.reduceEqDiff, Bool.not_false, Bool.not_true, Bool.and_true,
      Bool.and_false, Bool.false_eq_true, decide_true, decide_false, or_false, false_or, reduceIte, Nat.toUInt64,
      getElem!_pos input.incidence (index * input.categories + category) addressBound,
      addressWord, lengthWord, UInt64.mul_one] using next

#print axioms matrixRead_exact

end Project.Beck.Execution
