import Project.SumCount.Module
import Project.Pipeline.Implements
import Project.Pipeline.Allocation
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Project.ProofKit.FixedFrame

namespace Project.SumCount.Execution

open Wasm Project.Runtime Project.ProofKit Project.Pipeline

/-- The array-size computation before the allocation: 8 + 2 · 1 · 8 bytes,
rounded up to a multiple of 8 and at least 8. -/
def pre : Wasm.Program :=
  [.constI64 8, .constI64 2, .constI64 1, .mulI64, .constI64 8, .mulI64, .addI64,
   .constI64 7, .addI64, .constI64 8, .divUI64, .constI64 8, .mulI64, .localSet 11,
   .localGet 11, .constI64 8, .ltUI64,
   .iff 0 0 [.constI64 8, .localSet 11] [] [] []]

def loopBody : Wasm.Program :=
  [.localGet 13, .localGet 15, .geUI64, .br_if 1,
   .localGet 11, .localGet 13, .constI64 1, .mulI64, .constI64 1, .addI64, .constI64 8,
   .mulI64, .addI64, .wrapI64, .load64 0, .localSet 2,
   .localGet 1, .localGet 2, .addI64, .localSet 3,
   .localGet 3, .localSet 17,
   .constI64 0, .localSet 16,
   .localGet 17, .localSet 1,
   .localGet 16, .constI64 0, .neI64, .br_if 1,
   .localGet 13, .constI64 1, .addI64, .localSet 13,
   .br 0]

def postPrefix : Wasm.Program :=
  [.localGet 16, .localSet 7,
   .localGet 7, .wrapI64, .constI64 2, .store64 0,
   .localGet 0, .localSet 11,
   .localGet 11, .wrapI64, .load64 0, .localSet 12,
   .constI64 0, .localSet 13,
   .localGet 0, .localSet 16,
   .localGet 16, .wrapI64, .load64 0, .localSet 14,
   .constI64 0, .localSet 1,
   .localGet 14, .localGet 12, .ltUI64,
   .iff 0 1 [.localGet 14] [.localGet 12] [] [.i64],
   .localSet 15]

def afterLoop : Wasm.Program :=
  [.localGet 1, .localSet 10,
   .localGet 7, .constI64 0, .constI64 1, .mulI64, .constI64 1, .addI64, .constI64 8,
   .mulI64, .addI64, .wrapI64, .localGet 10, .store64 0,
   .localGet 0, .localSet 11,
   .localGet 11, .wrapI64, .load64 0, .localSet 10,
   .localGet 7, .constI64 1, .constI64 1, .mulI64, .constI64 1, .addI64, .constI64 8,
   .mulI64, .addI64, .wrapI64, .localGet 10, .store64 0,
   .localGet 7, .localSet 4,
   .localGet 4, .localSet 5,
   .localGet 4, .localSet 6,
   .localGet 6]

/-- Everything after the allocation: the length word, the fold over the input,
the two result words, and the return. -/
def post : Wasm.Program :=
  postPrefix ++ (.block 0 0 [.loop 0 0 loopBody [] []] [] [] :: afterLoop)

def entry : Wasm.Function :=
  { params := [.i64], locals := List.replicate 20 .i64,
    body := pre ++ (FixedArrayAllocate.program 11 1 ++ post),
    results := [.i64], typeIdx := some 0 }

theorem entry_lookup : sumModule.funcs[0 - sumModule.imports.length]? = some entry := by
  rfl

theorem memIs64 : sumModule.memIs64 = false := by
  rfl

def allocatedFrame (input previous current capacity next root : UInt64) : Locals :=
  FixedArraySearch.frame [.i64 input] (List.replicate 10 (.i64 0)) (List.replicate 4 (.i64 0))
    24 previous current capacity next root

/-- The locals at the head of the fold loop. -/
def loopFrame (input root len index acc v2 v3 v16 v17 : UInt64) : Locals :=
  { params := [.i64 input],
    locals := [.i64 acc, .i64 v2, .i64 v3, .i64 0, .i64 0, .i64 0, .i64 root, .i64 0, .i64 0,
      .i64 0, .i64 input, .i64 len, .i64 index, .i64 len, .i64 len, .i64 v16, .i64 v17,
      .i64 0, .i64 0, .i64 0],
    values := [] }

theorem wrap_address (x : UInt64) : UInt32.ofNat (x.toNat % 2 ^ 32) + 0 = x.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

theorem wrap_toNat (x : UInt64) : (UInt32.ofNat (x.toNat % 2 ^ 32)).toNat = x.toUInt32.toNat := by
  simp [UInt64.toNat_toUInt32]

theorem element_offset (i : Nat) : (UInt64.ofNat i * 1 + 1) * 8 = UInt64.ofNat (8 * (i + 1)) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_mul, UInt64.toNat_add, UInt64.toNat_ofNat']
  omega

theorem ofNat_succ (i : Nat) : UInt64.ofNat i + 1 = UInt64.ofNat (i + 1) := by
  apply UInt64.toNat_inj.mp
  simp [UInt64.toNat_add, UInt64.toNat_ofNat']

theorem ofNat_ge_ofNat {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNat a ≥ UInt64.ofNat b ↔ b ≤ a := by
  have ha' : a < 18446744073709551616 := ha
  have hb' : b < 18446744073709551616 := hb
  rw [ge_iff_le, UInt64.le_iff_toNat_le]
  simp only [UInt64.toNat_ofNat']
  omega

theorem loop_iteration (env : HostEnv Unit) (st : Store Unit) (input root : UInt64)
    (xs : Array UInt64) (hIn : UInt64Array.At st input xs) (i : Nat) (hi : i < xs.size)
    (acc v2 v3 v16 v17 : UInt64) (Q : Assertion Unit)
    (hNext : Q (.Break 0 st (loopFrame input root (UInt64.ofNat xs.size) (UInt64.ofNat (i + 1))
      (acc + xs[i]) xs[i] (acc + xs[i]) 0 (acc + xs[i])))) :
    wp sumModule loopBody Q st
      (loopFrame input root (UInt64.ofNat xs.size) (UInt64.ofNat i) acc v2 v3 v16 v17) env := by
  have hSize := hIn.1
  have hMemory := hIn.2.1
  have hLt : ¬ UInt64.ofNat i ≥ UInt64.ofNat xs.size := by
    rw [ofNat_ge_ofNat (by omega) (by omega)]
    omega
  have hAddress := UInt64Array.At.elementAddress_toNat hIn i hi
  have hRead := hIn.2.2.2 i hi
  simp only [loopBody, loopFrame]
  wp_fixed_frame
  simp only [hLt, ite_false, element_offset, wrap_toNat, hAddress, wrap_address, hRead,
    UInt32.toNat_zero, Nat.add_zero, ofNat_succ]
  split_ifs with hOut hZero
  · omega
  · exact absurd rfl hZero
  · exact hNext

theorem loop_exit (env : HostEnv Unit) (st : Store Unit) (input root len : UInt64)
    (acc v2 v3 v16 v17 : UInt64) (Q : Assertion Unit)
    (hExit : Q (.Break 1 st (loopFrame input root len len acc v2 v3 v16 v17))) :
    wp sumModule loopBody Q st (loopFrame input root len len acc v2 v3 v16 v17) env := by
  simp only [loopBody, loopFrame]
  wp_fixed_frame
  simp only [ge_iff_le, UInt64.le_refl, ite_true]
  exact hExit

def indexOf (locals : List Value) : Nat :=
  match locals[12]? with
  | some (Value.i64 v) => v.toNat
  | _ => 0

theorem indexOf_frame (input root len acc v2 v3 v16 v17 : UInt64) (i : Nat) (hi : i < 2 ^ 64) :
    indexOf (loopFrame input root len (UInt64.ofNat i) acc v2 v3 v16 v17).locals = i := by
  simp only [indexOf, loopFrame, List.getElem?_cons_succ, List.getElem?_cons_zero]
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt hi]

theorem fold_loop (env : HostEnv Unit) (st : Store Unit) (input root : UInt64)
    (xs : Array UInt64) (hIn : UInt64Array.At st input xs) (v16 : UInt64)
    (rest : Wasm.Program) (Q : Assertion Unit)
    (hRest : ∀ v2 v3 v16 v17 : UInt64, wp sumModule rest Q st
      (loopFrame input root (UInt64.ofNat xs.size) (UInt64.ofNat xs.size)
        (xs.foldl (· + ·) 0) v2 v3 v16 v17) env) :
    wp sumModule (.block 0 0 [.loop 0 0 loopBody [] []] [] [] :: rest) Q st
      (loopFrame input root (UInt64.ofNat xs.size) (UInt64.ofNat 0) 0 0 0 v16 0) env := by
  have hSize : xs.size < 2 ^ 64 := by have := hIn.1; omega
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ ∃ (i : Nat) (v2 v3 v16 v17 : UInt64), i ≤ xs.size ∧
      s = loopFrame input root (UInt64.ofNat xs.size) (UInt64.ofNat i)
        (ArrayFold.foldPrefix xs (· + ·) 0 i) v2 v3 v16 v17)
    (μ := fun _ s => xs.size - indexOf s.locals)
  · exact ⟨rfl, 0, 0, 0, v16, 0, Nat.zero_le _, by simp [ArrayFold.foldPrefix, loopFrame]⟩
  · rintro st' s ⟨rfl, i, v2, v3, v16, v17, hi, rfl⟩
    by_cases hLt : i < xs.size
    · apply loop_iteration env st' input root xs hIn i hLt
      refine ⟨⟨rfl, i + 1, xs[i], ArrayFold.foldPrefix xs (· + ·) 0 i + xs[i], 0,
        ArrayFold.foldPrefix xs (· + ·) 0 i + xs[i], hLt, ?_⟩, ?_⟩
      · simp [loopFrame, ArrayFold.foldPrefix_succ xs (· + ·) 0 i hLt]
      · dsimp only
        rw [indexOf_frame _ _ _ _ _ _ _ _ _ (by omega), indexOf_frame _ _ _ _ _ _ _ _ _ (by omega)]
        omega
    · obtain rfl : i = xs.size := by omega
      apply loop_exit
      show wp sumModule rest Q st' _ env
      rw [ArrayFold.foldPrefix_size]
      exact hRest v2 v3 v16 v17

theorem write64_pages (mem : Mem) (address : UInt32) (value : UInt64) :
    (mem.write64 address value).pages = mem.pages := rfl

theorem toUInt32_toNat_of_lt {x : UInt64} (h : x.toNat < 4294967296) :
    x.toUInt32.toNat = x.toNat := by
  simp [UInt64.toNat_toUInt32]
  omega

theorem post_prefix (env : HostEnv Unit) (st : Store Unit)
    (input root previous current capacity next : UInt64) (xs : Array UInt64)
    (hIn : UInt64Array.At { st with mem := st.mem.write64 root.toUInt32 2 } input xs)
    (hRoot : root.toNat + 8 ≤ st.mem.pages * 65536) (hRoot32 : root.toNat < 4294967296)
    (rest : Wasm.Program) (Q : Assertion Unit)
    (hRest : wp sumModule rest Q { st with mem := st.mem.write64 root.toUInt32 2 }
      (loopFrame input root (UInt64.ofNat xs.size) (UInt64.ofNat 0) 0 0 0 input 0) env) :
    wp sumModule (postPrefix ++ rest) Q st
      (allocatedFrame input previous current capacity next root) env := by
  have hInputBound := hIn.1
  have hInputMemory : input.toNat + 8 * (xs.size + 1) ≤ st.mem.pages * 65536 := hIn.2.1
  have hLength := hIn.2.2.1
  have hInput32 := toUInt32_toNat_of_lt (x := input) (by omega)
  have hRootAddress := toUInt32_toNat_of_lt hRoot32
  simp only [postPrefix, allocatedFrame, FixedArraySearch.frame, List.replicate, List.cons_append,
    List.nil_append]
  wp_fixed_frame
  simp only [wrap_toNat, wrap_address, write64_pages, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega)),
    ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
  simp only [hLength]
  refine wp_iff_cons rfl ?_
  simp only [UInt64.lt_irrefl, reduceIte, ne_eq, not_true_eq_false]
  wp_fixed_frame
  exact hRest

/-- The memory after the result array is filled in: the length 2 at `root`, then
`sum` and `count`. -/
def resultStore (st : Store Unit) (root sum count : UInt64) : Store Unit :=
  { st with
    mem := ((st.mem.write64 root.toUInt32 2).write64 (root + 8).toUInt32 sum).write64
      (root + 16).toUInt32 count }

theorem result_addresses {root : UInt64} (h : root.toNat + 24 ≤ 4294967296) :
    root.toUInt32.toNat = root.toNat ∧ (root + 8).toUInt32.toNat = root.toNat + 8 ∧
      (root + 16).toUInt32.toNat = root.toNat + 16 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [UInt64.toNat_toUInt32] <;> omega

theorem resultStore_writes (st : Store Unit) (root sum count : UInt64) (capacity : Nat)
    (hRoot32 : root.toNat + 24 ≤ 4294967296) (hCapacity : 24 ≤ capacity) :
    WritesWithin st (resultStore st root sum count) root.toNat capacity := by
  obtain ⟨h0, h8, h16⟩ := result_addresses hRoot32
  refine ⟨rfl, rfl, fun address hAddress => ?_⟩
  simp only [resultStore]
  rw [Memory.write64_bytes_outside _ _ _ (by omega), Memory.write64_bytes_outside _ _ _ (by omega),
    Memory.write64_bytes_outside _ _ _ (by omega)]

theorem resultStore_values (st : Store Unit) (root sum count : UInt64)
    (hRoot32 : root.toNat + 24 ≤ 4294967296) (hRoot : root.toNat + 24 ≤ st.mem.pages * 65536) :
    UInt64Array.At (resultStore st root sum count) root #[sum, count] := by
  obtain ⟨h0, h8, h16⟩ := result_addresses hRoot32
  apply UInt64Array.pair (store := resultStore st root sum count) hRoot32 hRoot <;>
    simp only [resultStore]
  · rw [Memory.read64_write64_disjoint _ _ _ _ (by omega),
      Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
  · rw [Memory.read64_write64_disjoint _ _ _ _ (by omega), Memory.read64_write64]
  · rw [Memory.read64_write64]

theorem after_loop (env : HostEnv Unit) (st : Store Unit) (input root : UInt64)
    (xs : Array UInt64) (acc v2 v3 v16 v17 : UInt64)
    (hIn : UInt64Array.At { st with mem := st.mem.write64 (root + 8).toUInt32 acc } input xs)
    (hRoot : root.toNat + 24 ≤ st.mem.pages * 65536) (hRoot32 : root.toNat + 24 ≤ 4294967296)
    (Q : Assertion Unit)
    (hQ : ∀ locals, Q (.Fallthrough
      { st with
        mem := (st.mem.write64 (root + 8).toUInt32 acc).write64 (root + 16).toUInt32
          (UInt64.ofNat xs.size) }
      { params := [.i64 input], locals := locals, values := [.i64 root] })) :
    wp sumModule afterLoop Q st
      (loopFrame input root (UInt64.ofNat xs.size) (UInt64.ofNat xs.size) acc v2 v3 v16 v17) env := by
  obtain ⟨_, h8, h16⟩ := result_addresses hRoot32
  have hInput32 := hIn.pointerAddress_toNat
  have hInputEnd : input.toNat + 8 * (xs.size + 1) ≤ st.mem.pages * 65536 := hIn.2.1
  have hLength : (st.mem.write64 (root + 8).toUInt32 acc).read64 input.toUInt32 =
      UInt64.ofNat xs.size := hIn.2.2.1
  simp only [afterLoop, loopFrame]
  wp_fixed_frame [UInt64.reduceMul, UInt64.reduceAdd]
  simp only [wrap_toNat, wrap_address, write64_pages, UInt32.toNat_zero, Nat.add_zero, h8, h16,
    hInput32, hLength]
  split_ifs <;> first | omega | exact hQ _

theorem post_spec (env : HostEnv Unit) (st : Store Unit)
    (input root previous current capacity next : UInt64) (xs : Array UInt64)
    (hIn : UInt64Array.At st input xs)
    (hSeparate : input.toNat + 8 * (xs.size + 1) ≤ root.toNat ∨ root.toNat + 24 ≤ input.toNat)
    (hRoot : root.toNat + 24 ≤ st.mem.pages * 65536) (hRoot32 : root.toNat + 24 ≤ 4294967296)
    (Q : Assertion Unit)
    (hQ : ∀ locals, Q (.Fallthrough (resultStore st root (xs.foldl (· + ·) 0) (UInt64.ofNat xs.size))
      { params := [.i64 input], locals := locals, values := [.i64 root] })) :
    wp sumModule post Q st (allocatedFrame input previous current capacity next root) env := by
  obtain ⟨h0, h8, _⟩ := result_addresses hRoot32
  have hIn1 : UInt64Array.At { st with mem := st.mem.write64 root.toUInt32 2 } input xs :=
    arrayAt_frame hIn (Nat.le_refl _) fun _ _ _ => Memory.write64_bytes_outside _ _ _ (by omega)
  have hIn2 : UInt64Array.At
      { st with
        mem := (st.mem.write64 root.toUInt32 2).write64 (root + 8).toUInt32 (xs.foldl (· + ·) 0) }
      input xs :=
    arrayAt_frame hIn1 (Nat.le_refl _) fun _ _ _ => Memory.write64_bytes_outside _ _ _ (by omega)
  unfold post
  apply post_prefix env st input root previous current capacity next xs hIn1 (by omega) (by omega)
  apply fold_loop env _ input root xs hIn1 input
  intro v2 v3 v16 v17
  exact after_loop env { st with mem := st.mem.write64 root.toUInt32 2 } input root xs
    (xs.foldl (· + ·) 0) v2 v3 v16 v17 hIn2 hRoot hRoot32 Q hQ

theorem implements : Implements sumModule 0 LeanExe.Examples.SumCount.sumCount fun _ => 72 := by
  intro env store heap params xs hHeap hArgs hRoom
  obtain ⟨input, rfl, hInput⟩ := hArgs
  show TerminatesWith env sumModule 0 store [.i64 input] _
  have hRoom' : heap.Room store sumModule (48 + (24 : UInt64).toNat) := hRoom
  have hBlock := hHeap.allocate_block 1 hRoom'
  have hAt0 := hHeap.allocate 1 hRoom'
  have hInput0 := hInput.allocate 1 hHeap hRoom'
  have hDisjoint := hInput.disjoint_allocated hHeap 24
  have hCapacity : 24 ≤ (allocatedCapacity 24 heap.free).toNat := allocated_capacity 24 heap.free
  have hSeparate := hDisjoint
  simp only [regionsDisjoint] at hSeparate
  have := hBlock.base
  have := hBlock.address
  have := hBlock.memory
  apply TerminatesWith.of_wp_entry_for entry_lookup
  show wp sumModule (pre ++ (FixedArrayAllocate.program 11 1 ++ post)) _ store
    { params := [.i64 input], locals := List.replicate 20 (Value.i64 0), values := [] } env
  simp only [pre, List.cons_append, List.nil_append, List.replicate]
  wp_fixed_frame [UInt64.reduceMul, UInt64.reduceAdd, UInt64.reduceDiv, UInt64.reduceLT]
  refine wp_iff_cons rfl ?_
  simp only [reduceIte, ne_eq, not_true_eq_false]
  wp_fixed_frame
  refine array_allocation_spec sumModule memIs64 env store heap [.i64 input]
    (List.replicate 10 (.i64 0)) (List.replicate 4 (.i64 0)) 11 rfl 24 1 0 0 0 0 0 hHeap hRoom'
    _ post fun previous current capacity next => ?_
  refine post_spec env _ input (FixedArrayAllocate.root heap.top 24 heap.free) previous current capacity next
    xs hInput0.values (by omega) (by omega) (by omega) _ fun locals => ?_
  have hWrites := resultStore_writes (heap.allocateStore store 24 1)
    (FixedArrayAllocate.root heap.top 24 heap.free) (xs.foldl (· + ·) 0) (UInt64.ofNat xs.size)
    (allocatedCapacity 24 heap.free).toNat (by omega) hCapacity
  dsimp only
  exact ⟨heap.allocate 24, hAt0.writesWithin hBlock hWrites,
    ⟨FixedArrayAllocate.root heap.top 24 heap.free, rfl,
      (hBlock.writesWithin hWrites).owned (resultStore_values _ _ _ _ (by omega) (by omega))
        (by simpa [LeanExe.Examples.SumCount.sumCount] using hCapacity)⟩,
    ⟨input, rfl, hInput0.writesWithin hDisjoint hWrites⟩,
    Heap.allocate_top hRoom', Heap.allocate_pages heap store 24 1⟩

end Project.SumCount.Execution
