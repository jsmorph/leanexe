import Project.Beck.ExecutionRoundBoundary
import Project.Beck.ExecutionWordPushLocal

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def roundUpdating : Wasm.Program := match (roundUsable[54]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

def roundBody : Wasm.Program := match (roundUpdating[59]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def roundPushLocals (locals : List Value) (length : Nat) : List Value :=
  ((locals.set 58 (.i64 length.toUInt64)).set 59 (.i64 length.toUInt64)).set 60 (.i64 (length + 1).toUInt64)

set_option maxRecDepth 4096 in
theorem round_push_shape : (roundBody.drop 38).take 67 = (roundBody.drop 38).take 12 ++ wordPushProgram 66 := rfl

set_option maxRecDepth 4096 in
theorem roundPushRead_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (ptr : UInt64) (words : Array UInt64) (paramsSize : params.length = 9) (localsSize : locals.length = 77)
    (pointerRead : locals[57]? = some (.i64 ptr)) (represented : UInt64Array.At initial ptr words)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := roundPushLocals locals words.size })) :
    wp Project.Beck.«module» ((roundBody.drop 38).take 12) Q initial { params := params, locals := locals } env := by
  have lengthRead : initial.mem.read64 (UInt32.ofNat (ptr.toNat % 2 ^ 32)) = words.size.toUInt64 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthRead
  have lengthBound : (UInt32.ofNat (ptr.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthBound
  have increment : words.size.toUInt64 + 1 = (words.size + 1).toUInt64 := (UInt64.ofNat_add _ _).symm
  simp only [roundBody, roundUpdating, roundUsable, func33, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, pointerRead,
    lengthRead, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, Nat.not_lt.mpr lengthBound, UInt64.mul_one, reduceIte]
  simpa only [roundPushLocals, increment] using next

set_option maxRecDepth 4096 in
theorem roundPush_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (typed : WordLocals locals) (paramsSize : params.length = 9) (localsSize : locals.length = 77)
    (ptr value : UInt64) (words : Array UInt64)
    (sourceRead : locals[57]? = some (.i64 ptr)) (valueRead : locals[63]? = some (.i64 value))
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
      ∀ nextLocals, WordUpdate locals nextLocals 57 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» ((roundBody.drop 38).take 67) Q initial { params := params, locals := locals } env := by
  let prepared := roundPushLocals locals words.size
  have update : WordUpdate locals prepared 57 15 :=
    (((WordUpdate.refl typed 57 15).set 58 words.size.toUInt64 (by omega) (by omega)).set
      59 words.size.toUInt64 (by omega) (by omega)).set 60 (words.size + 1).toUInt64 (by omega) (by omega)
  have preparedSize : prepared.length = 77 := update.size.trans localsSize
  rw [round_push_shape]
  refine Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared }) ?_ ?_
  · exact roundPushRead_exact env initial params locals ptr words paramsSize localsSize sourceRead represented _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  have sameProgram : wordPushProgram 66 = wordPushProgram (params.length + 57) := by rw [paramsSize]
  rw [sameProgram]
  apply wordPushLocal_exact env initial heap params prepared 57 update.words (by omega) ptr words value
  · simpa only [prepared, roundPushLocals, List.getElem?_set, List.length_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using sourceRead
  · simp [prepared, roundPushLocals, localsSize]
  · simp [prepared, roundPushLocals, localsSize]
  · simp [prepared, roundPushLocals, localsSize]
  · simpa only [prepared, roundPushLocals, List.getElem?_set, List.length_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using valueRead
  · exact valid
  · exact bound
  · exact represented
  · exact protects
  · exact budget
  · intro final
    dsimp only
    intro finalValid owned preserved fresh finalBudget nextLocals changed
    exact next final finalValid owned preserved fresh finalBudget nextLocals (update.trans changed)

#print axioms roundPush_exact

end Project.Beck.Execution
