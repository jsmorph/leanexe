import Project.Beck.ExecutionDirectionFirstRead
import Project.Beck.ExecutionWordUpdate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

theorem directionFirstLocals_update (locals : List Value) (typed : WordLocals locals)
    (ptr value : UInt64) (free size : Nat) :
    WordUpdate locals (directionFirstLocals locals ptr value free size) 49 55 := by
  exact ((((((WordUpdate.refl typed 49 55).set 49 ptr (by omega) (by omega)).set 50 free.toUInt64 (by omega) (by omega)).set
    89 ptr (by omega) (by omega)).set 90 free.toUInt64 (by omega) (by omega)).set
    95 value (by omega) (by omega)).set 91 size.toUInt64 (by omega) (by omega)

set_option maxRecDepth 4096 in
theorem direction_first_set_shape :
    directionSetFirst = directionSetFirst.take 4 ++ wordSetProgram 98 := rfl

set_option maxRecDepth 4096 in
theorem directionFirstSetBranch_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (typed : WordLocals locals) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ptr value : UInt64) (words : Array UInt64) (free : Nat)
    (sourceRead : locals[89]? = some (.i64 ptr)) (indexRead : locals[90]? = some (.i64 free.toUInt64))
    (lengthRead : locals[91]? = some (.i64 words.size.toUInt64)) (valueRead : locals[95]? = some (.i64 value))
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : words.size ≤ 56) (inside : free < words.size)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (words.set! free value) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate locals nextLocals 89 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» directionSetFirst Q initial { params := params, locals := locals } env := by
  let counted := locals.set 92 (.i64 words.size.toUInt64)
  have update : WordUpdate locals counted 89 15 := (WordUpdate.refl typed 89 15).set 92 words.size.toUInt64 (by omega) (by omega)
  have countedSize : counted.length = 112 := update.size.trans localsSize
  rw [direction_first_set_shape]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := counted })
  · exact directionFirstCount_exact env initial params locals words.size paramsSize localsSize lengthRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  have sameProgram : wordSetProgram 98 = wordSetProgram (params.length + 89) := by rw [paramsSize]
  rw [sameProgram]
  apply wordSetLocal_exact env initial heap params counted 89 update.words (by omega) ptr words free value
  · simpa only [counted, List.getElem?_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using sourceRead
  · simpa only [counted, List.getElem?_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using indexRead
  · simpa only [counted, List.getElem?_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using lengthRead
  · simp [counted, localsSize]
  · simpa only [counted, List.getElem?_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using valueRead
  · exact valid
  · exact bound
  · exact inside
  · exact represented
  · exact protects
  · exact budget
  · intro final
    dsimp only
    intro finalValid owned preserved fresh finalBudget nextLocals changed
    exact next final finalValid owned preserved fresh finalBudget nextLocals (update.trans changed)

set_option maxRecDepth 4096 in
theorem direction_first_shape : (directionEligible.drop 48).take 18 =
    (directionEligible.drop 48).take 17 ++ [.iff 0 1 directionSetFirst [.unreachable] [] [.i64]] := rfl

set_option maxRecDepth 4096 in
theorem directionFirstSet_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (typed : WordLocals locals) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ptr value : UInt64) (words : Array UInt64) (free : Nat)
    (pointerRead : locals[90]? = some (.i64 ptr)) (freeRead : locals[46]? = some (.i64 free.toUInt64))
    (valueRead : locals[33]? = some (.i64 value))
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : words.size ≤ 56) (inside : free < words.size)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (words.set! free value) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate locals nextLocals 49 55 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» ((directionEligible.drop 48).take 18) Q initial { params := params, locals := locals } env := by
  let prepared := directionFirstLocals locals ptr value free words.size
  have update : WordUpdate locals prepared 49 55 := directionFirstLocals_update locals typed ptr value free words.size
  have preparedSize : prepared.length = 112 := update.size.trans localsSize
  rw [direction_first_shape]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared, values := [.i32 1] })
  · exact directionFirstRead_exact env initial params locals ptr value words free paramsSize localsSize pointerRead freeRead valueRead represented inside _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  simp only [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte]
  apply directionFirstSetBranch_exact env initial heap params prepared update.words paramsSize preparedSize ptr value words free
  · simp [prepared, directionFirstLocals, localsSize]
  · simp [prepared, directionFirstLocals, localsSize]
  · simp [prepared, directionFirstLocals, localsSize]
  · simp [prepared, directionFirstLocals, localsSize]
  · exact valid
  · exact bound
  · exact inside
  · exact represented
  · exact protects
  · exact budget
  · intro final
    dsimp only
    intro finalValid owned preserved fresh finalBudget nextLocals changed
    rw [wp_nil]
    exact next final finalValid owned preserved fresh finalBudget nextLocals (update.trans (changed.widen 49 55 (by omega) (by omega)))

#print axioms directionFirstSetBranch_exact
#print axioms directionFirstSet_exact

end Project.Beck.Execution
