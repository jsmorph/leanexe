import Project.Beck.ExecutionDirectionBudget

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def roundDirectionLocals (locals : List Value) (root : UInt64) : List Value :=
  ((((locals.set 10 (.i64 root)).set 9 (.i64 root)).set 11 (.i64 root)).set 12 (.i64 root)).set 54 (.i64 root)

def roundUsable : Wasm.Program := match (func33[53]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

set_option maxRecDepth 4096 in
theorem roundDirectionPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64)
    (size : locals.length = 77) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := directionPreparedLocals locals input point inputOwner inputPointer pointOwner pointPointer
        values := (matrixParams input point inputOwner inputPointer pointOwner pointPointer).reverse })) :
    wp Project.Beck.«module» (func33.take 27) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  simp only [func33, List.take]
  wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
    size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem roundDirectionRead_exact (env : HostEnv Unit) (initial : Store Unit) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer root : UInt64) (words : Array UInt64)
    (size : locals.length = 77) (represented : UInt64Array.At initial root words) (wordsSize : words.size = input.jobs)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer
        locals := roundDirectionLocals locals root, values := [.i32 0] })) :
    wp Project.Beck.«module» ((func33.drop 28).take 25) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
        locals := locals, values := [.i64 root, .i64 root] } env := by
  have lengthRead : initial.mem.read64 (UInt32.ofNat (root.toNat % 2 ^ 32)) = input.jobs.toUInt64 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq, represented.lengthRead, wordsSize]
  have lengthBound : (UInt32.ofNat (root.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthBound
  simp only [func33, List.drop, List.take]
  repeat' first
    | wp_run [matrixParams, inputValues, pointValues, List.reverse_cons, List.reverse_nil, List.cons_append, List.nil_append,
        size, List.length_set, List.getElem?_set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, lengthRead, lengthBound,
        UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, Nat.not_lt.mpr lengthBound,
        show (1 : UInt64) ≠ 0 by decide, show (0 : UInt64) ≠ 1 by decide,
        show (1 : UInt32) ≠ 0 by decide, ne_eq, not_true_eq_false, not_false_eq_true,
        List.take, List.drop, List.append_nil, reduceIte]
    | (try simp only [wp_iff_control_types]
       refine wp_iff_cons rfl ?_
       simp only [show (1 : UInt32) ≠ 0 by decide, show (1 : UInt64) ≠ 0 by decide,
         show (0 : UInt64) ≠ 1 by decide, ne_eq, not_true_eq_false, not_false_eq_true, reduceIte])
  exact next

set_option maxRecDepth 4096 in
theorem round_start_shape : func33.take 53 = func33.take 27 ++ (.call 30 :: (func33.drop 28).take 25) := rfl

set_option maxRecDepth 4096 in
theorem roundStart_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap) (locals : List Value)
    (input : Input) (point : Point) (inputOwner inputPointer pointOwner pointPointer : UInt64) (remaining pageLimit : Nat)
    (size : locals.length = 77) (valid : heap.At initial) (supported : Project.Beck.State.Supported input)
    (nonempty : (Project.Beck.Counting.live input point).Nonempty)
    (pointArray : UInt64Array.At initial pointPointer point.numerators)
    (pointProtected : heap.Protects pointPointer.toNat (pointPointer.toNat + 8 * (point.numerators.size + 1)))
    (inputArray : UInt64Array.At initial inputPointer input.incidence)
    (inputProtected : heap.Protects inputPointer.toNat (inputPointer.toNat + 8 * (input.incidence.size + 1)))
    (pointSize : input.jobs ≤ point.numerators.size) (inputSize : input.incidence.size = input.jobs * input.categories)
    (categories : input.categories ≤ 8) (overlap : input.overlap ≤ 8)
    (budget : OutputBudget initial heap (directionMaxBytes + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final finalHeap node, finalHeap.At final → finalHeap.OwnsWords final node (direction input point) →
      heap.Frame initial finalHeap final → FreshFor heap node →
      OutputBudget final finalHeap remaining pageLimit Project.Beck.«module» →
      Q (.Fallthrough final
        { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer,
          locals := roundDirectionLocals (directionPreparedLocals locals input point inputOwner inputPointer pointOwner pointPointer) node.root,
          values := [.i32 0] })) :
    wp Project.Beck.«module» (func33.take 53) Q initial
      { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := locals } env := by
  let prepared := directionPreparedLocals locals input point inputOwner inputPointer pointOwner pointPointer
  have preparedSize : prepared.length = 77 := by simp [prepared, directionPreparedLocals, size]
  rw [round_start_shape]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame =
    { params := matrixParams input point inputOwner inputPointer pointOwner pointPointer, locals := prepared,
      values := (matrixParams input point inputOwner inputPointer pointOwner pointPointer).reverse })
  · exact roundDirectionPrepare_exact env initial locals input point inputOwner inputPointer pointOwner pointPointer size _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine wp_call_tw (direction_supported_exact env initial heap input point inputOwner inputPointer pointOwner pointPointer remaining pageLimit
    valid supported nonempty pointArray pointProtected inputArray inputProtected pointSize inputSize categories overlap
    (budget.mono (Nat.add_le_add_right (directionBytes_bound input point supported categories nonempty) remaining))) ?_
  rintro final values ⟨finalHeap, node, finalValid, finalOwned, finalFrame, fresh, finalBudget, rfl⟩
  apply roundDirectionRead_exact env final prepared input point inputOwner inputPointer pointOwner pointPointer node.root (direction input point)
    preparedSize finalOwned.buffer.values (Project.Beck.Direction.direction_size_nonzero input point supported.capacity supported.overlap nonempty).1
  exact next final finalHeap node finalValid finalOwned finalFrame fresh finalBudget

#print axioms roundStart_exact

end Project.Beck.Execution
