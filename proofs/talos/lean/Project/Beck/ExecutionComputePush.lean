import Project.Beck.ExecutionComputeState
import Project.Beck.ExecutionWordPushLocal

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def computePushLocals (locals : List Value) (length : Nat) : List Value :=
  ((locals.set 60 (.i64 length.toUInt64)).set 61 (.i64 length.toUInt64)).set 62 (.i64 (length + 1).toUInt64)

set_option maxRecDepth 4096 in
theorem compute_push_shape : (computeOutputBody.drop 35).take 67 = (computeOutputBody.drop 35).take 12 ++ wordPushProgram 60 := rfl

set_option maxRecDepth 4096 in
theorem computePushRead_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (ptr : UInt64) (words : Array UInt64) (paramsSize : params.length = 1) (localsSize : locals.length = 79)
    (pointerRead : locals[59]? = some (.i64 ptr)) (represented : UInt64Array.At initial ptr words)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := computePushLocals locals words.size })) :
    wp Project.Beck.«module» ((computeOutputBody.drop 35).take 12) Q initial { params := params, locals := locals } env := by
  have lengthRead : initial.mem.read64 (UInt32.ofNat (ptr.toNat % 2 ^ 32)) = words.size.toUInt64 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthRead
  have lengthBound : (UInt32.ofNat (ptr.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthBound
  have increment : words.size.toUInt64 + 1 = (words.size + 1).toUInt64 := (UInt64.ofNat_add _ _).symm
  simp only [computeOutputBody, computeOutput, computeAccepted, func35, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, pointerRead,
    lengthRead, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, Nat.not_lt.mpr lengthBound, UInt64.mul_one, reduceIte]
  simpa only [computePushLocals, increment] using next

set_option maxRecDepth 4096 in
theorem computePush_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (typed : WordLocals locals) (paramsSize : params.length = 1) (localsSize : locals.length = 79)
    (ptr value : UInt64) (words : Array UInt64)
    (sourceRead : locals[59]? = some (.i64 ptr)) (valueRead : locals[65]? = some (.i64 value))
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : words.size ≤ 55)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 2) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 2))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (words.push value) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate locals nextLocals 59 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» ((computeOutputBody.drop 35).take 67) Q initial { params := params, locals := locals } env := by
  let prepared := computePushLocals locals words.size
  have update : WordUpdate locals prepared 59 15 :=
    (((WordUpdate.refl typed 59 15).set 60 words.size.toUInt64 (by omega) (by omega)).set
      61 words.size.toUInt64 (by omega) (by omega)).set 62 (words.size + 1).toUInt64 (by omega) (by omega)
  have preparedSize : prepared.length = 79 := update.size.trans localsSize
  rw [compute_push_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared }) ?_ ?_
  · exact computePushRead_exact env initial params locals ptr words paramsSize localsSize sourceRead represented _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  have sameProgram : wordPushProgram 60 = wordPushProgram (params.length + 59) := by rw [paramsSize]
  rw [sameProgram]
  apply wordPushLocal_exact env initial heap params prepared 59 update.words (by omega) ptr words value
  · simpa only [prepared, computePushLocals, List.getElem?_set, List.length_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using sourceRead
  · simp [prepared, computePushLocals, localsSize]
  · simp [prepared, computePushLocals, localsSize]
  · simp [prepared, computePushLocals, localsSize]
  · simpa only [prepared, computePushLocals, List.getElem?_set, List.length_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using valueRead
  · exact valid
  · exact bound
  · exact represented
  · exact protects
  · exact budget
  · intro final
    dsimp only
    intro finalValid owned preserved fresh finalBudget nextLocals changed
    exact next final finalValid owned preserved fresh finalBudget nextLocals (update.trans changed)

#print axioms computePush_exact

end Project.Beck.Execution
