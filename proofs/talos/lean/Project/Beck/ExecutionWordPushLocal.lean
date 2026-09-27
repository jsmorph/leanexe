import Project.Beck.ExecutionWordPush
import Project.Beck.ExecutionWordUpdate

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

theorem WordLocals.pushFrame {locals : List Value} (typed : WordLocals locals) (params : List Value)
    (offset : Nat) (bound : offset + 15 ≤ locals.length) (ptr value : UInt64) (length : Nat)
    (sourceRead : locals[offset]? = some (.i64 ptr))
    (lengthRead : locals[offset + 1]? = some (.i64 length.toUInt64))
    (countRead : locals[offset + 2]? = some (.i64 length.toUInt64))
    (nextRead : locals[offset + 3]? = some (.i64 (length + 1).toUInt64))
    (valueRead : locals[offset + 6]? = some (.i64 value)) :
    ∃ target counter padding1 padding2 need previous current capacity afterNode result : UInt64,
      ({ params := params, locals := locals } : Locals) =
        wordPushFrame params (locals.take offset) (locals.drop (offset + 15)) ptr length target counter value padding1 padding2
          need previous current capacity afterNode result := by
  obtain ⟨target, read4⟩ := typed.read (offset + 4) (by omega)
  obtain ⟨counter, read5⟩ := typed.read (offset + 5) (by omega)
  obtain ⟨padding1, read7⟩ := typed.read (offset + 7) (by omega)
  obtain ⟨padding2, read8⟩ := typed.read (offset + 8) (by omega)
  obtain ⟨need, read9⟩ := typed.read (offset + 9) (by omega)
  obtain ⟨previous, read10⟩ := typed.read (offset + 10) (by omega)
  obtain ⟨current, read11⟩ := typed.read (offset + 11) (by omega)
  obtain ⟨capacity, read12⟩ := typed.read (offset + 12) (by omega)
  obtain ⟨afterNode, read13⟩ := typed.read (offset + 13) (by omega)
  obtain ⟨result, read14⟩ := typed.read (offset + 14) (by omega)
  refine ⟨target, counter, padding1, padding2, need, previous, current, capacity, afterNode, result, ?_⟩
  apply Frame.ext <;> try rfl
  have split := locals_window_eq locals
    [.i64 ptr, .i64 length.toUInt64, .i64 length.toUInt64, .i64 (length + 1).toUInt64,
      .i64 target, .i64 counter, .i64 value, .i64 padding1, .i64 padding2, .i64 need, .i64 previous,
      .i64 current, .i64 capacity, .i64 afterNode, .i64 result] offset (by
      intro i hi
      simp only [List.length_cons, List.length_nil] at hi
      interval_cases i <;> simp only [Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
        sourceRead, lengthRead, countRead, nextRead, valueRead, read4, read5, read7, read8, read9, read10, read11, read12, read13, read14])
  simpa only [wordPushFrame, FixedArraySearch.frame, List.length_cons, List.length_nil, Nat.reduceAdd,
    List.append_assoc, List.cons_append, List.nil_append] using split

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem wordPushLocal_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (offset : Nat) (typed : WordLocals locals) (windowBound : offset + 15 ≤ locals.length)
    (ptr : UInt64) (words : Array UInt64) (value : UInt64)
    (sourceRead : locals[offset]? = some (.i64 ptr))
    (lengthRead : locals[offset + 1]? = some (.i64 words.size.toUInt64))
    (countRead : locals[offset + 2]? = some (.i64 words.size.toUInt64))
    (nextRead : locals[offset + 3]? = some (.i64 (words.size + 1).toUInt64))
    (valueRead : locals[offset + 6]? = some (.i64 value))
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
      ∀ nextLocals, WordUpdate locals nextLocals offset 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» (wordPushProgram (params.length + offset)) Q initial { params := params, locals := locals } env := by
  obtain ⟨target, counter, padding1, padding2, need, previous, current, capacity, afterNode, result, frameEq⟩ :=
    typed.pushFrame params offset windowBound ptr value words.size sourceRead lengthRead countRead nextRead valueRead
  have takeSize : (locals.take offset).length = offset := by simp [List.length_take, Nat.min_eq_left (by omega : offset ≤ locals.length)]
  rw [frameEq]
  simpa only [List.append_nil] using wordPush_exact env initial heap params (locals.take offset) (locals.drop (offset + 15))
    (params.length + offset) (by rw [takeSize]) ptr words target counter value padding1 padding2 need previous current capacity afterNode result
    remaining pageLimit valid bound represented protects budget Q [] (by
      intro final
      dsimp only
      intro finalValid owned preserved fresh finalBudget previous current capacity afterNode
      rw [wp_nil]
      apply next final finalValid owned preserved fresh finalBudget
      have windowTyped : WordLocals
          [.i64 ptr, .i64 words.size.toUInt64, .i64 words.size.toUInt64, .i64 (words.size + 1).toUInt64,
            .i64 (allocatedRoot heap.top (UInt64.ofNat (8 * (words.size + 2))) heap.nodes), .i64 words.size.toUInt64,
            .i64 value, .i64 padding1, .i64 padding2, .i64 (UInt64.ofNat (8 * (words.size + 2))),
            .i64 previous, .i64 current, .i64 capacity, .i64 afterNode,
            .i64 (allocatedRoot heap.top (UInt64.ofNat (8 * (words.size + 2))) heap.nodes)] := by
        repeat' apply WordLocals.cons
        exact WordLocals.nil
      have update := wordWindow_update locals _ offset typed windowTyped (by simpa using windowBound)
      simpa only [wordPushFrame, FixedArraySearch.frame, allocatedNode, List.length_cons, List.length_nil, Nat.reduceAdd,
        List.append_assoc, List.cons_append, List.nil_append] using update)

#print axioms wordPushLocal_exact

end Project.Beck.Execution
