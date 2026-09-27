import Project.Beck.ExecutionDirectionColumn
import Project.ProofKit.CheckedArrayGet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

def directionCoefficientPrepared (locals : List Value) (current columns value : UInt64) (index : Nat) : List Value :=
  ((((locals.set 72 (.i64 value)).set 73 (.i64 value)).set 74 (.i64 current)).set 92 (.i64 columns)).set 93 (.i64 index.toUInt64)

def directionCoefficientLocals (locals : List Value) (current columns value column : UInt64) (index : Nat) : List Value :=
  let l := directionCoefficientPrepared locals current columns value index
  (((l.set 75 (.i64 column)).set 92 (.i64 current)).set 93 (.i64 column)).set 98 (.i64 (0 - value))

theorem directionCoefficientLocals_words (locals : List Value) (typed : WordLocals locals)
    (current columns value column : UInt64) (index : Nat) :
    WordLocals (directionCoefficientLocals locals current columns value column index) := by
  unfold directionCoefficientLocals directionCoefficientPrepared
  repeat' apply WordLocals.set
  exact typed

set_option maxRecDepth 4096 in
theorem directionCoefficientPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (current columns value : UInt64) (index : Nat)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (columnsRead : locals[32]? = some (.i64 columns)) (currentRead : locals[58]? = some (.i64 current))
    (indexRead : locals[56]? = some (.i64 index.toUInt64)) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := directionCoefficientPrepared locals current columns value index })) :
    wp Project.Beck.«module» ((directionBody.drop 58).take 9) Q initial
      { params := params, locals := locals, values := [.i64 value] } env := by
  simp only [directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, columnsRead, currentRead, indexRead, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem directionCoefficientStage_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (current column value : UInt64) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (currentRead : locals[74]? = some (.i64 current)) (valueRead : locals[73]? = some (.i64 value)) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := params, locals := (((locals.set 75 (.i64 column)).set 92 (.i64 current)).set 93 (.i64 column)).set 98 (.i64 (0 - value)) })) :
    wp Project.Beck.«module» ((directionBody.drop 73).take 9) Q initial
      { params := params, locals := locals, values := [.i64 column] } env := by
  simp only [directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, currentRead, valueRead, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem direction_coefficient_read_shape : (directionBody.drop 58).take 24 =
    (directionBody.drop 58).take 9 ++ (CheckedArrayGet.checkedGetCore 101 102 ++ (directionBody.drop 73).take 9) := rfl

set_option maxRecDepth 4096 in
theorem directionCoefficientRead_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (current columns value : UInt64) (words : Array UInt64) (index : Nat) (inside : index < words.size)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (columnsRead : locals[32]? = some (.i64 columns)) (currentRead : locals[58]? = some (.i64 current))
    (indexRead : locals[56]? = some (.i64 index.toUInt64)) (represented : UInt64Array.At initial columns words)
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := params, locals := directionCoefficientLocals locals current columns value words[index] index })) :
    wp Project.Beck.«module» ((directionBody.drop 58).take 24) Q initial
      { params := params, locals := locals, values := [.i64 value] } env := by
  let prepared := directionCoefficientPrepared locals current columns value index
  have preparedSize : prepared.length = 112 := by simp [prepared, directionCoefficientPrepared, localsSize]
  rw [direction_coefficient_read_shape]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared })
  · exact directionCoefficientPrepare_exact env initial params locals current columns value index paramsSize localsSize columnsRead currentRead indexRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  refine CheckedArrayGet.checkedGetCore_spec 101 102 Project.Beck.«module» env initial _ columns words index [] ?_ ?_ rfl represented inside Q _ ?_
  · simp [Locals.get, paramsSize, prepared, directionCoefficientPrepared, localsSize]
  · simp [Locals.get, paramsSize, prepared, directionCoefficientPrepared, localsSize]
  · apply directionCoefficientStage_exact env initial params prepared current words[index] value paramsSize preparedSize
    · simp [prepared, directionCoefficientPrepared, localsSize]
    · simp [prepared, directionCoefficientPrepared, localsSize]
    · exact next

set_option maxRecDepth 4096 in
theorem direction_coefficient_shape : (directionBody.drop 58).take 32 =
    (directionBody.drop 58).take 24 ++ (directionBody.drop 82).take 8 := rfl

set_option maxRecDepth 4096 in
theorem directionCoefficient_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (typed : WordLocals locals) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ptr columns value : UInt64) (words indices : Array UInt64) (index : Nat) (indexBound : index < indices.size)
    (columnsRead : locals[32]? = some (.i64 columns)) (currentRead : locals[58]? = some (.i64 ptr))
    (indexRead : locals[56]? = some (.i64 index.toUInt64)) (indicesAt : UInt64Array.At initial columns indices)
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : words.size ≤ 56) (inside : indices[index].toNat < words.size)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (words.set! indices[index].toNat (0 - value)) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate (directionCoefficientLocals locals ptr columns value indices[index] index) nextLocals 92 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» ((directionBody.drop 58).take 32) Q initial
      { params := params, locals := locals, values := [.i64 value] } env := by
  let prepared := directionCoefficientLocals locals ptr columns value indices[index] index
  have preparedSize : prepared.length = 112 := by simp [prepared, directionCoefficientLocals, directionCoefficientPrepared, localsSize]
  have preparedWords : WordLocals prepared := directionCoefficientLocals_words locals typed ptr columns value indices[index] index
  rw [direction_coefficient_shape, direction_replacement_shapes.2.2]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared })
  · exact directionCoefficientRead_exact env initial params locals ptr columns value indices index indexBound paramsSize localsSize columnsRead currentRead indexRead indicesAt _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply directionReplacement_exact env initial heap params prepared preparedWords paramsSize preparedSize ptr (0 - value) words indices[index].toNat
  · simp [prepared, directionCoefficientLocals, directionCoefficientPrepared, localsSize]
  · simp [prepared, directionCoefficientLocals, directionCoefficientPrepared, localsSize]
  · simp [prepared, directionCoefficientLocals, directionCoefficientPrepared, localsSize]
  · exact valid
  · exact bound
  · exact inside
  · exact represented
  · exact protects
  · exact budget
  · exact next

#print axioms directionCoefficientRead_exact
#print axioms directionCoefficient_exact

end Project.Beck.Execution
