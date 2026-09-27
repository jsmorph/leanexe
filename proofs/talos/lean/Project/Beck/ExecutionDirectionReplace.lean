import Project.Beck.ExecutionDirectionFirstSet

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

set_option maxRecDepth 4096 in
theorem direction_replacement_shapes :
    directionSetColumn = directionSetColumn.take 4 ++ wordSetProgram 101 ∧
    (directionBody.drop 18).take 8 = (directionBody.drop 18).take 7 ++
      [.iff 0 1 directionSetColumn [.unreachable] [] [.i64]] ∧
    (directionBody.drop 82).take 8 = (directionBody.drop 18).take 8 := ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
theorem directionReplacementCount_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (length : Nat) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (lengthRead : locals[94]? = some (.i64 length.toUInt64)) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial { params := params, locals := locals.set 95 (.i64 length.toUInt64) })) :
    wp Project.Beck.«module» (directionSetColumn.take 4) Q initial { params := params, locals := locals } env := by
  simp only [directionSetColumn, directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.take]
  wp_run [paramsSize, localsSize, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, lengthRead, UInt64.mul_one, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem directionReplacementBranch_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (typed : WordLocals locals) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ptr value : UInt64) (words : Array UInt64) (index : Nat)
    (sourceRead : locals[92]? = some (.i64 ptr)) (indexRead : locals[93]? = some (.i64 index.toUInt64))
    (lengthRead : locals[94]? = some (.i64 words.size.toUInt64)) (valueRead : locals[98]? = some (.i64 value))
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : words.size ≤ 56) (inside : index < words.size)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (words.set! index value) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate locals nextLocals 92 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» directionSetColumn Q initial { params := params, locals := locals } env := by
  let counted := locals.set 95 (.i64 words.size.toUInt64)
  have update : WordUpdate locals counted 92 15 := (WordUpdate.refl typed 92 15).set 95 words.size.toUInt64 (by omega) (by omega)
  have countedSize : counted.length = 112 := update.size.trans localsSize
  rw [direction_replacement_shapes.1]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := counted })
  · exact directionReplacementCount_exact env initial params locals words.size paramsSize localsSize lengthRead _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  have sameProgram : wordSetProgram 101 = wordSetProgram (params.length + 92) := by rw [paramsSize]
  rw [sameProgram]
  apply wordSetLocal_exact env initial heap params counted 92 update.words (by omega) ptr words index value
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
theorem directionReplacementRead_exact (env : HostEnv Unit) (initial : Store Unit) (params locals : List Value)
    (ptr : UInt64) (words : Array UInt64) (index : Nat)
    (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (pointerRead : locals[92]? = some (.i64 ptr)) (indexRead : locals[93]? = some (.i64 index.toUInt64))
    (represented : UInt64Array.At initial ptr words) (inside : index < words.size) (Q : Assertion Unit)
    (next : Q (.Fallthrough initial
      { params := params, locals := locals.set 94 (.i64 words.size.toUInt64), values := [.i32 1] })) :
    wp Project.Beck.«module» ((directionBody.drop 18).take 7) Q initial { params := params, locals := locals } env := by
  have lengthRead : initial.mem.read64 (UInt32.ofNat (ptr.toNat % 2 ^ 32)) = UInt64.ofNat words.size := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthRead
  have lengthBound : (UInt32.ofNat (ptr.toNat % 2 ^ 32)).toNat + 8 ≤ initial.mem.pages * 65536 := by
    simp only [Nat.reducePow]; rw [represented.pointerAddress_eq]; exact represented.lengthBound
  have wordInside : index.toUInt64 < words.size.toUInt64 := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (inside.trans represented.size_lt), UInt64.toNat_ofNat_of_lt' represented.size_lt]
    exact inside
  simp only [directionBody, directionEligible, func30, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.take]
  wp_run [paramsSize, localsSize, List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceEqDiff, pointerRead, indexRead,
    lengthRead, UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero, Nat.not_lt.mpr lengthBound, wordInside, reduceIte]
  exact next

set_option maxRecDepth 4096 in
theorem directionReplacement_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (typed : WordLocals locals) (paramsSize : params.length = 9) (localsSize : locals.length = 112)
    (ptr value : UInt64) (words : Array UInt64) (index : Nat)
    (pointerRead : locals[92]? = some (.i64 ptr)) (indexRead : locals[93]? = some (.i64 index.toUInt64))
    (valueRead : locals[98]? = some (.i64 value))
    (remaining pageLimit : Nat) (valid : heap.At initial) (bound : words.size ≤ 56) (inside : index < words.size)
    (represented : UInt64Array.At initial ptr words)
    (protects : heap.Protects ptr.toNat (ptr.toNat + 8 * (words.size + 1)))
    (budget : OutputBudget initial heap (48 + 8 * (words.size + 1) + remaining) pageLimit Project.Beck.«module»)
    (Q : Assertion Unit)
    (next : ∀ final,
      let size := UInt64.ofNat (8 * (words.size + 1))
      let node := allocatedNode heap.top size heap.nodes
      (heap.allocate size).At final → (heap.allocate size).OwnsWords final node (words.set! index value) →
      heap.Frame initial (heap.allocate size) final → FreshFor heap node →
      OutputBudget final (heap.allocate size) remaining pageLimit Project.Beck.«module» →
      ∀ nextLocals, WordUpdate locals nextLocals 92 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» ((directionBody.drop 18).take 8) Q initial { params := params, locals := locals } env := by
  let prepared := locals.set 94 (.i64 words.size.toUInt64)
  have update : WordUpdate locals prepared 92 15 := (WordUpdate.refl typed 92 15).set 94 words.size.toUInt64 (by omega) (by omega)
  have preparedSize : prepared.length = 112 := update.size.trans localsSize
  rw [direction_replacement_shapes.2.1]
  apply Sequence.wp_append (P := fun store frame => store = initial ∧ frame = { params := params, locals := prepared, values := [.i32 1] })
  · exact directionReplacementRead_exact env initial params locals ptr words index paramsSize localsSize pointerRead indexRead represented inside _ ⟨rfl, rfl⟩
  rintro store frame ⟨same, frameSame⟩
  subst store frame
  simp only [wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  simp only [show (1 : UInt32) ≠ 0 by decide, ne_eq, not_false_eq_true, reduceIte]
  apply directionReplacementBranch_exact env initial heap params prepared update.words paramsSize preparedSize ptr value words index
  · simpa only [prepared, List.getElem?_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using pointerRead
  · simpa only [prepared, List.getElem?_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using indexRead
  · simp [prepared, localsSize]
  · simpa only [prepared, List.getElem?_set, localsSize, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] using valueRead
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
    exact next final finalValid owned preserved fresh finalBudget nextLocals (update.trans changed)

#print axioms directionReplacement_exact

end Project.Beck.Execution
