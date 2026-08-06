import Project.ProofKit.Allocation
import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit.FixedArrayAllocator

open Wasm

macro "wp_alloc_run" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals,
      List.take, List.drop, List.replicate, List.length, List.map,
      List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Wasm.ValueType.zero, List.headD, $ts,*])

def searchBody (stride : UInt64) : Wasm.Program :=
  [
  .localGet 11,
  .constI64 0,
  .eqI64,
  .br_if 1,
  .localGet 14,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 11,
  .constI64 32,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 12,
  .localGet 11,
  .constI64 8,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 13,
  .localGet 12,
  .localGet 9,
  .geUI64,
  .iff 0 0 [
    .localGet 10,
    .constI64 0,
    .eqI64,
    .iff 0 0 [
      .localGet 13,
      .globalSet 1
    ] [
      .localGet 10,
      .constI64 8,
      .subI64,
      .wrapI64,
      .localGet 13,
      .store64 0
    ],
    .localGet 11,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 11,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 11,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 12,
    .store64 0,
    .localGet 11,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 11,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 stride,
    .store64 0,
    .localGet 11,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0,
    .localGet 11,
    .localSet 14
  ] [
    .localGet 11,
    .localSet 10,
    .localGet 13,
    .localSet 11
  ],
  .br 0
  ]

def search (stride : UInt64) : Wasm.Program :=
  [.block 0 0 [.loop 0 0 (searchBody stride)]]

def bump (stride : UInt64) : Wasm.Program :=
  [
  .localGet 14,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localGet 9,
    .addI64,
    .localSet 12,
    .localGet 12,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [.unreachable] [],
    .localGet 12,
    .constI64 1,
    .subI64,
    .constI64 65536,
    .divUI64,
    .constI64 1,
    .addI64,
    .localSet 13,
    .memorySize,
    .extendUI32,
    .localGet 13,
    .ltUI64,
    .iff 0 0 [
      .localGet 13,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const 4294967295,
      .eq,
      .iff 0 0 [.unreachable] []
    ] [],
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localSet 14,
    .localGet 12,
    .globalSet 0,
    .localGet 14,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 14,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 14,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 9,
    .store64 0,
    .localGet 14,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 14,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 stride,
    .store64 0,
    .localGet 14,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0
  ] []
  ]

def finish : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 14,
  .localSet 5
  ]

def region (stride : UInt64) : Wasm.Program :=
  [
  .constI64 0,
  .localSet 14,
  .constI64 0,
  .localSet 10,
  .globalGet 1,
  .localSet 11
  ] ++ search stride ++ bump stride ++ finish

def headerMem (mem : Mem) (base capacity stride : UInt64) : Mem :=
  (((((mem.write64
    (UInt32.ofNat (base.toNat % 4294967296)) 5501223100278326855).write64
    (UInt32.ofNat ((base.toNat + 8) % 4294967296)) 1).write64
    (UInt32.ofNat ((base.toNat + 16) % 4294967296)) capacity).write64
    (UInt32.ofNat ((base.toNat + 24) % 4294967296)) 2).write64
    (UInt32.ofNat ((base.toNat + 32) % 4294967296)) stride).write64
    (UInt32.ofNat ((base.toNat + 40) % 4294967296)) 0

def allocStore (st : Store Unit) (base capacity stride allocs : UInt64) : Store Unit :=
  let globals :=
    (st.globals.globals.set 0 (.i64 (base + 48 + capacity))).set 2
      (.i64 (allocs + 1))
  { st with
    globals := { globals := globals }
    mem := headerMem st.mem base capacity stride }

def searchFrame (base : Locals) : Locals :=
  { base with
    locals := ((base.locals.set 13 (.i64 0)).set 9 (.i64 0)).set 10 (.i64 0) }

def allocFrame (base : Locals) (heapTop capacity : UInt64) : Locals :=
  { base with
    locals := ((((((base.locals.set 13 (.i64 0)).set 9 (.i64 0)).set 10
      (.i64 0)).set 11 (.i64 (heapTop + 48 + capacity))).set 12
      (.i64 ((heapTop + 48 + capacity - 1) / 65536 + 1))).set 13
      (.i64 (heapTop + 48))).set 4 (.i64 (heapTop + 48)) }

theorem allocStore_pages (st : Store Unit) (base capacity stride allocs : UInt64) :
    (allocStore st base capacity stride allocs).mem.pages = st.mem.pages := by
  simp [allocStore, headerMem, Mem.write64_pages]

set_option Elab.async false in
theorem region_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop capacity stride allocs : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 14)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.locals[8]? = some (.i64 capacity))
    (hCapacity : 8 ≤ capacity.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (allocStore st heapTop capacity stride allocs)
      (allocFrame frame heapTop capacity) env) :
    wp module_ (region stride ++ rest) Q st frame env := by
  have hCapacityGet : frame.locals[8] = .i64 capacity := by
    have h := hCapacityLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [region, search, bump, finish, List.cons_append, List.nil_append]
  wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
  simp only [hFreeList]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = searchFrame frame)
    (μ := fun _ _ => 0)
  · refine ⟨rfl, ?_⟩
    simp [searchFrame, hValues]
  · rintro st1 s1 ⟨hSt, hFrame⟩
    subst st1
    subst s1
    simp only [searchBody, searchFrame]
    wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
    simp only [hHeapTop]
    have hFacts := Project.ProofKit.Allocation.bumpFacts heapTop capacity
      st.mem.pages hFitMemory hPages
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hFacts.noOverflow)]
    wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
    rw [hMemory32]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hFacts.noGrow)]
    wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
    simp only [hHeapTop]
    try wp_alloc_run [hParams, hLocals, hValues, hCapacityGet]
    try simp
    have hBaseBound : heapTop.toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase8Bound : (heapTop + 48 - 40).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header40ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase16Bound : (heapTop + 48 - 32).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header32ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase24Bound : (heapTop + 48 - 24).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header24ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase32Bound : (heapTop + 48 - 16).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header16ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase40Bound : (heapTop + 48 - 8).toNat % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
      rw [hFacts.header8ToNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_neg (Nat.not_lt.mpr hBaseBound),
      if_neg (Nat.not_lt.mpr hBase8Bound),
      if_neg (Nat.not_lt.mpr hBase16Bound),
      if_neg (Nat.not_lt.mpr hBase24Bound),
      if_neg (Nat.not_lt.mpr hBase32Bound),
      if_neg (Nat.not_lt.mpr hBase40Bound)]
    simp only [hAllocs]
    simpa only [allocStore, allocFrame, headerMem,
      Project.ProofKit.Memory.toUInt32_eq_ofNat, hFacts.rootToNat,
      hFacts.header40ToNat, hFacts.header32ToNat, hFacts.header24ToNat,
      hFacts.header16ToNat, hFacts.header8ToNat, hValues] using hNext

end Project.ProofKit.FixedArrayAllocator
