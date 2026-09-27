import Project.Beck.ExecutionWordSetWindow

namespace Project.Beck.Execution

open Wasm Project.ProofKit Project.Runtime Project.EulerRiemann.Execution

structure WordUpdate (before after : List Value) (offset count : Nat) : Prop where
  size : after.length = before.length
  words : WordLocals after
  keeps : ∀ index, index < offset ∨ offset + count ≤ index → after[index]? = before[index]?

theorem WordUpdate.refl {locals : List Value} (typed : WordLocals locals) (offset count : Nat) :
    WordUpdate locals locals offset count := ⟨rfl, typed, fun _ _ => rfl⟩

theorem WordUpdate.set {before after : List Value} {offset count : Nat}
    (update : WordUpdate before after offset count) (index : Nat) (value : UInt64)
    (lower : offset ≤ index) (upper : index < offset + count) :
    WordUpdate before (after.set index (.i64 value)) offset count := by
  refine ⟨by simpa using update.size, update.words.set index value, ?_⟩
  intro other outside
  rw [List.getElem?_set_ne (by omega : index ≠ other)]
  exact update.keeps other outside

theorem WordUpdate.widen {before after : List Value} {offset count : Nat}
    (update : WordUpdate before after offset count) (start length : Nat)
    (lower : start ≤ offset) (upper : offset + count ≤ start + length) :
    WordUpdate before after start length :=
  ⟨update.size, update.words, fun index outside => update.keeps index (by omega)⟩

theorem WordUpdate.trans {before middle after : List Value} {offset count : Nat}
    (first : WordUpdate before middle offset count) (second : WordUpdate middle after offset count) :
    WordUpdate before after offset count :=
  ⟨second.size.trans first.size, second.words, fun index outside =>
    (second.keeps index outside).trans (first.keeps index outside)⟩

theorem wordWindow_update (locals window : List Value) (offset : Nat) (typed : WordLocals locals)
    (windowWords : WordLocals window) (bound : offset + window.length ≤ locals.length) :
    WordUpdate locals (locals.take offset ++ window ++ locals.drop (offset + window.length)) offset window.length := by
  have takeSize : (locals.take offset).length = offset := by simp [List.length_take, Nat.min_eq_left (by omega : offset ≤ locals.length)]
  refine ⟨?_, ((typed.take offset).append windowWords).append (typed.drop _), ?_⟩
  · simp only [List.length_append, takeSize, List.length_drop]
    omega
  · intro index outside
    rcases outside with before | after
    · rw [List.getElem?_append_left (by simp only [List.length_append, takeSize]; omega),
        List.getElem?_append_left (by omega), List.getElem?_take_of_lt before]
    · rw [List.getElem?_append_right (by simp only [List.length_append, takeSize]; omega)]
      simp only [List.length_append, takeSize, List.getElem?_drop]
      congr 1
      omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem wordSetLocal_exact (env : HostEnv Unit) (initial : Store Unit) (heap : Heap)
    (params locals : List Value) (offset : Nat) (typed : WordLocals locals) (windowBound : offset + 15 ≤ locals.length)
    (ptr : UInt64) (words : Array UInt64) (index : Nat) (value : UInt64)
    (sourceRead : locals[offset]? = some (.i64 ptr))
    (indexRead : locals[offset + 1]? = some (.i64 index.toUInt64))
    (lengthRead : locals[offset + 2]? = some (.i64 words.size.toUInt64))
    (countRead : locals[offset + 3]? = some (.i64 words.size.toUInt64))
    (valueRead : locals[offset + 6]? = some (.i64 value))
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
      ∀ nextLocals, WordUpdate locals nextLocals offset 15 →
      Q (.Fallthrough final { params := params, locals := nextLocals, values := [.i64 node.root] })) :
    wp Project.Beck.«module» (wordSetProgram (params.length + offset)) Q initial { params := params, locals := locals } env := by
  obtain ⟨target, counter, padding1, padding2, need, previous, current, capacity, afterNode, result, frameEq⟩ :=
    typed.setFrame params offset windowBound ptr value index words.size sourceRead indexRead lengthRead countRead valueRead
  have takeSize : (locals.take offset).length = offset := by simp [List.length_take, Nat.min_eq_left (by omega : offset ≤ locals.length)]
  rw [frameEq]
  simpa only [List.append_nil] using wordSet_exact env initial heap params (locals.take offset) (locals.drop (offset + 15))
    (params.length + offset) (by rw [takeSize]) ptr words index target counter value padding1 padding2 need previous current capacity afterNode result
    remaining pageLimit valid bound inside represented protects budget Q [] (by
      intro final
      dsimp only
      intro finalValid owned preserved fresh finalBudget previous current capacity afterNode
      rw [wp_nil]
      apply next final finalValid owned preserved fresh finalBudget
      have windowTyped : WordLocals
          [.i64 ptr, .i64 index.toUInt64, .i64 words.size.toUInt64, .i64 words.size.toUInt64,
            .i64 (allocatedRoot heap.top (UInt64.ofNat (8 * (words.size + 1))) heap.nodes), .i64 words.size.toUInt64,
            .i64 value, .i64 padding1, .i64 padding2, .i64 (UInt64.ofNat (8 * (words.size + 1))),
            .i64 previous, .i64 current, .i64 capacity, .i64 afterNode,
            .i64 (allocatedRoot heap.top (UInt64.ofNat (8 * (words.size + 1))) heap.nodes)] := by
        repeat' apply WordLocals.cons
        exact WordLocals.nil
      have update := wordWindow_update locals _ offset typed windowTyped (by simpa using windowBound)
      simpa only [wordSetFrame, FixedArraySearch.frame, allocatedNode, List.length_cons, List.length_nil, Nat.reduceAdd,
        List.append_assoc, List.cons_append, List.nil_append] using update)

#print axioms wordSetLocal_exact

end Project.Beck.Execution
