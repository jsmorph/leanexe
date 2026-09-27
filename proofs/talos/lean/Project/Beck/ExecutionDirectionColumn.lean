import Project.Beck.ExecutionDirectionReplace
import Project.Beck.ExecutionDirectionLoopStart

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution LeanExe.Examples.Beck

def directionColumnLocals (locals : List Value) (columns current : UInt64) (free index : Nat) : List Value :=
  let l := (((locals.set 56 (.i64 index.toUInt64)).set 58 (.i64 current)).set 59 (.i64 columns)).set 60 (.i64 index.toUInt64)
  ((l.set 92 (.i64 columns)).set 93 (.i64 index.toUInt64)).set 98 (.i64 free.toUInt64)

theorem directionColumnLocals_update (locals : List Value) (typed : WordLocals locals)
    (columns current : UInt64) (free index : Nat) :
    WordUpdate locals (directionColumnLocals locals columns current free index) 56 51 := by
  unfold directionColumnLocals
  exact (((((((WordUpdate.refl typed 56 51).set 56 index.toUInt64 (by omega) (by omega)).set 58 current (by omega) (by omega)).set
    59 columns (by omega) (by omega)).set 60 index.toUInt64 (by omega) (by omega)).set 92 columns (by omega) (by omega)).set
    93 index.toUInt64 (by omega) (by omega)).set 98 free.toUInt64 (by omega) (by omega)

set_option maxRecDepth 4096 in
theorem directionColumnPrepare_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (columns current : UInt64) (free index : Nat)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (columnsRead : locals[32]? = some (.i64 columns)) (currentRead : locals[55]? = some (.i64 current))
    (freeRead : locals[46]? = some (.i64 free.toUInt64)) (indexRead : locals[89]? = some (.i64 index.toUInt64))
    (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := directionColumnLocals locals columns current free index })) :
    wp Project.Beck.«module» ((directionBody.drop 4).take 14) Q initial { params := params, locals := locals } env := by
  simp only [directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, columnsRead, currentRead, freeRead, indexRead, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem direction_column_shape : (directionBody.drop 4).take 22 =
    (directionBody.drop 4).take 14 ++ (directionBody.drop 18).take 8 := rfl

set_option maxRecDepth 4096 in
theorem directionColumn_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (typed : WordLocals locals) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ptr current : UInt64) (columns : Array UInt64) (free index : Nat)
    (columnsRead : locals[32]? = some (.i64 ptr)) (currentRead : locals[55]? = some (.i64 current))
    (freeRead : locals[46]? = some (.i64 free.toUInt64)) (indexRead : locals[89]? = some (.i64 index.toUInt64))
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : columns.size ≤ 56) (inside : index < columns.size)
    (represented : UInt64Array.At initial ptr columns)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (columns.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (columns.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (columns.size + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (columns.set! index free.toUInt64) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate (directionColumnLocals locals ptr current free index) nextLocals 92 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» ((directionBody.drop 4).take 22) Q initial { params := params, locals := locals } env := by
  let prepared := directionColumnLocals locals ptr current free index
  have update : WordUpdate locals prepared 56 51 := directionColumnLocals_update locals typed ptr current free index
  have preparedSize : prepared.length = 112 := update.size.trans localsSize
  rw [direction_column_shape]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared })
  · exact directionColumnPrepare_exact env initial params locals ptr current free index paramsSize localsSize columnsRead currentRead freeRead indexRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  apply directionReplacement_exact env initial heap params prepared update.words paramsSize preparedSize ptr free.toUInt64 columns index
  · simp [prepared, directionColumnLocals, localsSize]
  · simp [prepared, directionColumnLocals, localsSize]
  · simp [prepared, directionColumnLocals, localsSize]
  · exact valid
  · exact bound
  · exact inside
  · exact represented
  · exact protects
  · exact budget
  · exact next

#print axioms directionColumn_exact

end Project.Beck.Execution
