import LeanExeGen.GeneratedReb06c2a75684e92c.FormalSpec
import LeanExeGen.GeneratedReb06c2a75684e92c.Program
import Project.ProofKit.Array
import Project.ProofKit.Allocation
import Project.ProofKit.Control

set_option maxRecDepth 1048576
set_option maxHeartbeats 1000000

namespace LeanExeGen.GeneratedReb06c2a75684e92c.Behavior

open Wasm

namespace Allocator

macro "wp_alloc_run24" "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    simp (config := { maxSteps := 10000000 }) [wp_simp,
      Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
      Wasm.Function.toLocals, Wasm.Function.numParams,
      Wasm.Function.numLocals,
      List.take, List.drop, List.replicate, List.length, List.map,
      List.length_set, List.getElem?_set,
      Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
      Wasm.ValueType.zero, List.headD, $ts,*])

def searchBody : Wasm.Program :=
  [
  .localGet 21,
  .constI64 0,
  .eqI64,
  .br_if 1,
  .localGet 24,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 21,
  .constI64 32,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 22,
  .localGet 21,
  .constI64 8,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 23,
  .localGet 22,
  .localGet 19,
  .geUI64,
  .iff 0 0 [
    .localGet 20,
    .constI64 0,
    .eqI64,
    .iff 0 0 [
      .localGet 23,
      .globalSet 1
    ] [
      .localGet 20,
      .constI64 8,
      .subI64,
      .wrapI64,
      .localGet 23,
      .store64 0
    ],
    .localGet 21,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 21,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 21,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 22,
    .store64 0,
    .localGet 21,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 21,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 21,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0,
    .localGet 21,
    .localSet 24
  ] [
    .localGet 21,
    .localSet 20,
    .localGet 23,
    .localSet 21
  ],
  .br 0
  ]

def search : Wasm.Program :=
  [.block 0 0 [.loop 0 0 searchBody]]

def bump : Wasm.Program :=
  [
  .localGet 24,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localGet 19,
    .addI64,
    .localSet 22,
    .localGet 22,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [.unreachable] [],
    .localGet 22,
    .constI64 1,
    .subI64,
    .constI64 65536,
    .divUI64,
    .constI64 1,
    .addI64,
    .localSet 23,
    .memorySize,
    .extendUI32,
    .localGet 23,
    .ltUI64,
    .iff 0 0 [
      .localGet 23,
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
    .localSet 24,
    .localGet 22,
    .globalSet 0,
    .localGet 24,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 24,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 24,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 19,
    .store64 0,
    .localGet 24,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 24,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 24,
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
  .localGet 24,
  .localSet 15
  ]

def region : Wasm.Program :=
  [
  .constI64 0,
  .localSet 24,
  .constI64 0,
  .localSet 20,
  .globalGet 1,
  .localSet 21
  ] ++ search ++ bump ++ finish

def headerMem (mem : Mem) (base capacity : UInt64) : Mem :=
  (((((mem.write64
    (UInt32.ofNat (base.toNat % 4294967296)) 5501223100278326855).write64
    (UInt32.ofNat ((base.toNat + 8) % 4294967296)) 1).write64
    (UInt32.ofNat ((base.toNat + 16) % 4294967296)) capacity).write64
    (UInt32.ofNat ((base.toNat + 24) % 4294967296)) 2).write64
    (UInt32.ofNat ((base.toNat + 32) % 4294967296)) 1).write64
    (UInt32.ofNat ((base.toNat + 40) % 4294967296)) 0

def allocStore (st : Store Unit) (base capacity allocs : UInt64) : Store Unit :=
  let globals :=
    (st.globals.globals.set 0 (.i64 (base + 48 + capacity))).set 2
      (.i64 (allocs + 1))
  { st with
    globals := { globals := globals }
    mem := headerMem st.mem base capacity }

def searchFrame (base : Locals) : Locals :=
  { base with
    locals := ((base.locals.set 23 (.i64 0)).set 19 (.i64 0)).set 20 (.i64 0) }

def allocFrame (base : Locals) (heapTop capacity : UInt64) : Locals :=
  { base with
    locals := ((((((base.locals.set 23 (.i64 0)).set 19 (.i64 0)).set 20
      (.i64 0)).set 21 (.i64 (heapTop + 48 + capacity))).set 22
      (.i64 ((heapTop + 48 + capacity - 1) / 65536 + 1))).set 23
      (.i64 (heapTop + 48))).set 14 (.i64 (heapTop + 48)) }

theorem allocStore_pages (st : Store Unit) (base capacity allocs : UInt64) :
    (allocStore st base capacity allocs).mem.pages = st.mem.pages := by
  simp [allocStore, headerMem, Mem.write64_pages]

set_option Elab.async false in
theorem region_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop capacity allocs : UInt64)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hCapacityLocal : frame.locals[18]? = some (.i64 capacity))
    (hCapacity : 8 ≤ capacity.toNat)
    (hFitMemory : heapTop.toNat + 48 + capacity.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (allocStore st heapTop capacity allocs)
      (allocFrame frame heapTop capacity) env) :
    wp module_ (region ++ rest) Q st frame env := by
  have hCapacityGet : frame.locals[18] = .i64 capacity := by
    have h := hCapacityLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [region, search, bump, finish, List.cons_append, List.nil_append]
  wp_alloc_run24 [hParams, hLocals, hValues, hCapacityGet]
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
    wp_alloc_run24 [hParams, hLocals, hValues, hCapacityGet]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_alloc_run24 [hParams, hLocals, hValues, hCapacityGet]
    simp only [hHeapTop]
    have hFacts := Project.ProofKit.Allocation.bumpFacts heapTop capacity
      st.mem.pages hFitMemory hPages
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hFacts.noOverflow)]
    wp_alloc_run24 [hParams, hLocals, hValues, hCapacityGet]
    rw [hMemory32]
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hFacts.noGrow)]
    wp_alloc_run24 [hParams, hLocals, hValues, hCapacityGet]
    simp only [hHeapTop]
    try wp_alloc_run24 [hParams, hLocals, hValues, hCapacityGet]
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

end Allocator

def capacityPrefix : Wasm.Program :=
  [
  .constI64 8,
  .constI64 2,
  .constI64 1,
  .mulI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .constI64 7,
  .addI64,
  .constI64 8,
  .divUI64,
  .constI64 8,
  .mulI64,
  .localSet 19,
  .localGet 19,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 19
  ] []
  ]

def capacityFrame (frame : Locals) : Locals :=
  { frame with locals := frame.locals.set 18 (.i64 24) }

theorem capacityPrefix_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q st (capacityFrame frame) env) :
    wp module_ (capacityPrefix ++ rest) Q st frame env := by
  simp (config := { maxSteps := 10000000 }) [capacityPrefix, capacityFrame,
    wp_simp, Wasm.Locals.get, Wasm.Locals.set?, Wasm.Locals.validIndex,
    List.length_set, List.getElem?_set, hParams, hLocals, hValues]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  simpa [capacityFrame, hValues] using hNext

def pairConstSuffix (first second : UInt64) (destination : Nat) : Wasm.Program :=
  [
  .localGet 15,
  .wrapI64,
  .constI64 2,
  .store64 0,
  .constI64 first,
  .localSet 18,
  .localGet 15,
  .constI64 0,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 18,
  .store64 0,
  .constI64 second,
  .localSet 18,
  .localGet 15,
  .constI64 1,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 18,
  .store64 0,
  .localGet 15,
  .localSet destination,
  .localGet destination,
  .localSet 14
  ]

def constResultProgram (first second : UInt64) (destination : Nat) : Wasm.Program :=
  capacityPrefix ++ Allocator.region ++ pairConstSuffix first second destination

def pairPost (first second : UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame => ∃ outputPtr,
        frame.values = [] ∧
        frame.params.length = 1 ∧
        frame.locals.length = 24 ∧
        frame.locals[13]? = some (.i64 outputPtr) ∧
        Project.ProofKit.UInt64Array.At final outputPtr #[first, second]
    | _ => False

open Allocator

set_option Elab.async false in
theorem constResultProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop allocs first second : UInt64) (destination : Nat)
    (hParams : frame.params.length = 1)
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hFitMemory : heapTop.toNat + 48 + 24 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs)) :
    wp module_ (constResultProgram first second destination)
      (pairPost first second) st frame env := by
  unfold constResultProgram
  rw [List.append_assoc]
  apply capacityPrefix_spec module_ env st frame hParams hLocals hValues
  apply Allocator.region_spec module_ env st (capacityFrame frame)
    heapTop 24 allocs
  · simpa [capacityFrame] using hParams
  · simpa [capacityFrame] using hLocals
  · simpa [capacityFrame] using hValues
  · simp [capacityFrame, hLocals]
  · decide
  · simpa using hFitMemory
  · exact hPages
  · exact hMemory32
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · have hFacts := Project.ProofKit.Allocation.bumpFacts heapTop 24
      st.mem.pages (by simpa using hFitMemory) hPages
    have hFit32 : heapTop.toNat + 48 + 24 ≤ 4294967296 := by
      simpa using hFacts.fit32
    have hRootAddress := hFacts.wordAddress 0 (by decide)
    have hFirstAddress := hFacts.wordAddress 1 (by decide)
    have hSecondAddress := hFacts.wordAddress 2 (by decide)
    have hRootAddressNat := hFacts.wordAddress_toNat 0 (by decide)
    have hFirstAddressNat := hFacts.wordAddress_toNat 1 (by decide)
    have hSecondAddressNat := hFacts.wordAddress_toNat 2 (by decide)
    have hRootToNat32 : (heapTop + 48).toUInt32.toNat =
        heapTop.toNat + 48 := by
      simpa using hRootAddressNat
    have hFirstToNat32 : (heapTop + 48 + 8).toUInt32.toNat =
        heapTop.toNat + 48 + 8 := by
      simpa using hFirstAddressNat
    have hSecondToNat32 : (heapTop + 48 + 16).toUInt32.toNat =
        heapTop.toNat + 48 + 16 := by
      simpa using hSecondAddressNat
    have hRoot64 : heapTop.toNat + 48 < 18446744073709551616 := by omega
    have hRootAddress' : UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
        (heapTop + 48).toUInt32 := by
      simpa [Nat.mod_eq_of_lt hRoot64] using hRootAddress
    have hFirstAddress' : UInt32.ofNat ((heapTop.toNat + 48 + 8) % 4294967296) =
        (heapTop + 48 + 8).toUInt32 := by
      simpa [Nat.mod_eq_of_lt hRoot64] using hFirstAddress
    have hSecondAddress' : UInt32.ofNat ((heapTop.toNat + 48 + 16) % 4294967296) =
        (heapTop + 48 + 16).toUInt32 := by
      simpa [Nat.mod_eq_of_lt hRoot64] using hSecondAddress
    have hRootBound : (heapTop.toNat + 48) % 4294967296 + 8 ≤
        (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
      rw [Allocator.allocStore_pages, Nat.mod_eq_of_lt (by omega)]
      omega
    have hFirstBound : (heapTop.toNat + 48 + 8) % 4294967296 + 8 ≤
        (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
      rw [Allocator.allocStore_pages, Nat.mod_eq_of_lt (by omega)]
      omega
    have hSecondBound : (heapTop.toNat + 48 + 16) % 4294967296 + 8 ≤
        (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
      rw [Allocator.allocStore_pages, Nat.mod_eq_of_lt (by omega)]
      omega
    simp only [pairConstSuffix, List.cons_append, List.nil_append]
    wp_alloc_run24 [Allocator.allocFrame, capacityFrame, hParams, hLocals,
      hValues, hDestinationPositive, hDestination,
      hFacts.rootToNat, hRootAddress, hFirstAddress, hSecondAddress,
      hRootAddressNat, hFirstAddressNat, hSecondAddressNat]
    rw [if_neg (Nat.not_lt.mpr hRootBound),
      if_neg (Nat.not_lt.mpr hFirstBound),
      if_neg (Nat.not_lt.mpr hSecondBound)]
    have hDestinationLocal : destination - 1 < 24 := by omega
    simp (config := { maxSteps := 10000000 }) [pairPost, hParams, hLocals,
      hDestinationPositive.ne', hDestination, hDestinationLocal,
      List.getElem?_set]
    uint64_array_pair
    · rw [hFacts.rootToNat]
      omega
    · simp only [Mem.write64_pages, Allocator.allocStore_pages, hFacts.rootToNat]
      omega
    · rw [hRootAddress', hFirstAddress', hSecondAddress']
      word_reads
    · rw [hRootAddress', hFirstAddress', hSecondAddress']
      word_reads
    · rw [hRootAddress', hFirstAddress', hSecondAddress']
      word_reads

def pairInputSuffix (index destination : Nat) : Wasm.Program :=
  [
  .localGet 15,
  .wrapI64,
  .constI64 2,
  .store64 0,
  .localGet 0,
  .localSet 19,
  .constI64 (UInt64.ofNat index),
  .localSet 20,
  .localGet 20,
  .localGet 19,
  .wrapI64,
  .load64 0,
  .ltUI64,
  .iff 0 1 [
    .localGet 19,
    .localGet 20,
    .constI64 1,
    .mulI64,
    .constI64 1,
    .addI64,
    .constI64 8,
    .mulI64,
    .addI64,
    .wrapI64,
    .load64 0
  ] [
    .unreachable
  ],
  .localSet 18,
  .localGet 15,
  .constI64 0,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 18,
  .store64 0,
  .constI64 1,
  .localSet 18,
  .localGet 15,
  .constI64 1,
  .constI64 1,
  .mulI64,
  .constI64 1,
  .addI64,
  .constI64 8,
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 18,
  .store64 0,
  .localGet 15,
  .localSet destination,
  .localGet destination,
  .localSet 14
  ]

def inputResultProgram (index destination : Nat) : Wasm.Program :=
  capacityPrefix ++ Allocator.region ++ pairInputSuffix index destination

set_option Elab.async false in
theorem inputResultProgram_spec
    (module_ : Wasm.Module) (env : HostEnv Unit) (st : Store Unit) (frame : Locals)
    (heapTop allocs inputPtr : UInt64) (input : Array UInt64)
    (index destination : Nat)
    (hParamsValue : frame.params = [.i64 inputPtr])
    (hLocals : frame.locals.length = 24)
    (hValues : frame.values = [])
    (hDestinationPositive : 0 < destination)
    (hDestination : destination < 25)
    (hInput : Project.ProofKit.UInt64Array.At st inputPtr input)
    (hIndex : index < input.size)
    (hInputBelow : inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat)
    (hFitMemory : heapTop.toNat + 48 + 24 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hMemory32 : module_.memIs64 = false)
    (hHeapTop : st.globals.globals[0]? = some (.i64 heapTop))
    (hFreeList : st.globals.globals[1]? = some (.i64 0))
    (hAllocs : st.globals.globals[2]? = some (.i64 allocs)) :
    wp module_ (inputResultProgram index destination)
      (pairPost input[index] 1) st frame env := by
  have hParams : frame.params.length = 1 := by simp [hParamsValue]
  unfold inputResultProgram
  rw [List.append_assoc]
  apply capacityPrefix_spec module_ env st frame hParams hLocals hValues
  apply Allocator.region_spec module_ env st (capacityFrame frame)
    heapTop 24 allocs
  · simpa [capacityFrame] using hParams
  · simpa [capacityFrame] using hLocals
  · simpa [capacityFrame] using hValues
  · simp [capacityFrame, hLocals]
  · decide
  · simpa using hFitMemory
  · exact hPages
  · exact hMemory32
  · exact hHeapTop
  · exact hFreeList
  · exact hAllocs
  · have hFacts := Project.ProofKit.Allocation.bumpFacts heapTop 24
      st.mem.pages (by simpa using hFitMemory) hPages
    have hFit32 : heapTop.toNat + 48 + 24 ≤ 4294967296 := by
      simpa using hFacts.fit32
    have hRootAddress := hFacts.wordAddress 0 (by decide)
    have hFirstAddress := hFacts.wordAddress 1 (by decide)
    have hSecondAddress := hFacts.wordAddress 2 (by decide)
    have hRootAddressNat := hFacts.wordAddress_toNat 0 (by decide)
    have hFirstAddressNat := hFacts.wordAddress_toNat 1 (by decide)
    have hSecondAddressNat := hFacts.wordAddress_toNat 2 (by decide)
    have hRootToNat32 : (heapTop + 48).toUInt32.toNat =
        heapTop.toNat + 48 := by
      simpa using hRootAddressNat
    have hFirstToNat32 : (heapTop + 48 + 8).toUInt32.toNat =
        heapTop.toNat + 48 + 8 := by
      simpa using hFirstAddressNat
    have hSecondToNat32 : (heapTop + 48 + 16).toUInt32.toNat =
        heapTop.toNat + 48 + 16 := by
      simpa using hSecondAddressNat
    have hRoot64 : heapTop.toNat + 48 < 18446744073709551616 := by omega
    have hRootAddress' : UInt32.ofNat ((heapTop.toNat + 48) % 4294967296) =
        (heapTop + 48).toUInt32 := by
      simpa [Nat.mod_eq_of_lt hRoot64] using hRootAddress
    have hFirstAddress' : UInt32.ofNat ((heapTop.toNat + 48 + 8) % 4294967296) =
        (heapTop + 48 + 8).toUInt32 := by
      simpa [Nat.mod_eq_of_lt hRoot64] using hFirstAddress
    have hSecondAddress' : UInt32.ofNat ((heapTop.toNat + 48 + 16) % 4294967296) =
        (heapTop + 48 + 16).toUInt32 := by
      simpa [Nat.mod_eq_of_lt hRoot64] using hSecondAddress
    have hRootBound : (heapTop.toNat + 48) % 4294967296 + 8 ≤
        (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
      rw [Allocator.allocStore_pages, Nat.mod_eq_of_lt (by omega)]
      omega
    have hFirstBound : (heapTop.toNat + 48 + 8) % 4294967296 + 8 ≤
        (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
      rw [Allocator.allocStore_pages, Nat.mod_eq_of_lt (by omega)]
      omega
    have hSecondBound : (heapTop.toNat + 48 + 16) % 4294967296 + 8 ≤
        (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
      rw [Allocator.allocStore_pages, Nat.mod_eq_of_lt (by omega)]
      omega
    have hInputAlloc : Project.ProofKit.UInt64Array.At
        (Allocator.allocStore st heapTop 24 allocs) inputPtr input := by
      apply hInput.frameBefore hInputBelow
      · exact Allocator.allocStore_pages st heapTop 24 allocs
      · intro address hAddress
        simp only [Allocator.allocStore, Allocator.headerMem]
        rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
          simp [Nat.mod_eq_of_lt (by omega)]
          omega)]
        rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
          simp [Nat.mod_eq_of_lt (by omega)]
          omega)]
        rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
          simp [Nat.mod_eq_of_lt (by omega)]
          omega)]
        rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
          simp [Nat.mod_eq_of_lt (by omega)]
          omega)]
        rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
          simp [Nat.mod_eq_of_lt (by omega)]
          omega)]
        rw [Project.ProofKit.Memory.write64_bytes_before _ _ _ (by
          simp [Nat.mod_eq_of_lt (by omega)]
          omega)]
    have hInputAfterLength := hInputAlloc.write64After (address :=
      UInt32.ofNat ((heapTop.toNat + 48) % 4294967296)) (value := 2) (by
        rw [hRootAddress']
        rw [hRootToNat32]
        omega)
    have hLengthRead := hInputAfterLength.lengthRead
    have hLengthBound := hInputAfterLength.lengthBound
    have hInputAddress := hInputAfterLength.pointerAddress_eq
    have hValueRead := hInputAfterLength.elementRead index hIndex
    have hValueBound := hInputAfterLength.elementBound index hIndex
    have hValueAddress := hInputAfterLength.elementAddress_eq index hIndex
    have hValueAddress' :
        UInt32.ofNat ((inputPtr.toNat + (index + 1) * 8) % 4294967296) =
          (inputPtr + UInt64.ofNat (8 * (index + 1))).toUInt32 := by
      simpa [Nat.mul_comm] using hValueAddress
    have hIndex64 : index < UInt64.size := by
      have hSize := hInputAfterLength.size_lt
      omega
    have hIndexToNat : (UInt64.ofNat index).toNat = index :=
      UInt64.toNat_ofNat_of_lt' hIndex64
    have hInputSizeToNat : (UInt64.ofNat input.size).toNat = input.size :=
      UInt64.toNat_ofNat_of_lt' hInputAfterLength.size_lt
    have hIndexEncoded : UInt64.ofNat index < UInt64.ofNat input.size := by
      rw [UInt64.lt_iff_toNat_lt, hIndexToNat, hInputSizeToNat]
      exact hIndex
    have hLengthBound' : inputPtr.toNat % 4294967296 + 8 ≤
        (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
      simpa [Project.ProofKit.Memory.toUInt32_toNat] using hLengthBound
    have hValueBound' :
        (inputPtr.toNat + (index + 1) * 8) % 4294967296 + 8 ≤
          (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
      have hBound :
          (UInt32.ofNat ((inputPtr.toNat + 8 * (index + 1)) %
            4294967296)).toNat + 8 ≤
            (Allocator.allocStore st heapTop 24 allocs).mem.pages * 65536 := by
        rw [hValueAddress]
        exact hValueBound
      simpa [Nat.mul_comm] using hBound
    simp only [pairInputSuffix, List.cons_append, List.nil_append]
    wp_alloc_run24 [Allocator.allocFrame, capacityFrame, hParamsValue,
      hParams, hLocals, hValues, hDestinationPositive, hDestination,
      hFacts.rootToNat, hRootAddress, hFirstAddress, hSecondAddress,
      hRootAddressNat, hFirstAddressNat, hSecondAddressNat,
      hLengthRead, hLengthBound, hInputAddress, hValueRead, hValueBound,
      hValueAddress, hIndexToNat, hIndex]
    rw [if_neg (Nat.not_lt.mpr hRootBound)]
    rw [if_neg (Nat.not_lt.mpr hLengthBound')]
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hIndexEncoded])]
    wp_alloc_run24 [Allocator.allocFrame, capacityFrame, hParamsValue,
      hParams, hLocals, hValues, hDestinationPositive, hDestination,
      hFacts.rootToNat, hRootAddress, hFirstAddress, hSecondAddress,
      hRootAddressNat, hFirstAddressNat, hSecondAddressNat,
      hLengthRead, hLengthBound, hInputAddress, hValueRead, hValueBound,
      hValueAddress, hIndexToNat, hIndex]
    rw [if_neg (Nat.not_lt.mpr hValueBound')]
    rw [if_neg (Nat.not_lt.mpr hFirstBound),
      if_neg (Nat.not_lt.mpr hSecondBound)]
    have hDestinationLocal : destination - 1 < 24 := by omega
    simp (config := { maxSteps := 10000000 }) [pairPost, hParamsValue,
      hLocals, hDestinationPositive.ne', hDestination,
      hDestinationLocal, List.getElem?_set]
    rw [hValueAddress', hValueRead]
    uint64_array_pair
    · rw [hFacts.rootToNat]
      omega
    · simp only [Mem.write64_pages, Allocator.allocStore_pages,
        hFacts.rootToNat]
      omega
    · rw [hRootAddress', hFirstAddress', hSecondAddress']
      word_reads
    · rw [hRootAddress', hFirstAddress', hSecondAddress']
      word_reads
    · rw [hRootAddress', hFirstAddress', hSecondAddress']
      word_reads

def publicPost (input : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame => ∃ outputPtr,
        frame.values.take 1 = [.i64 outputPtr] ∧
        FormalSpec.UInt64ArrayAt final outputPtr (FormalSpec.expected input)
    | .Return final values => ∃ outputPtr,
        values.take 1 = [.i64 outputPtr] ∧
        FormalSpec.UInt64ArrayAt final outputPtr (FormalSpec.expected input)
    | _ => False

def fallthroughPost (module_ : Wasm.Module) (env : HostEnv Unit)
    (input : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame =>
        wp module_ [.localGet 14] (publicPost input) final
          { frame with values := [] } env
    | _ => False

def resultContinuation (module_ : Wasm.Module) (env : HostEnv Unit)
    (input : Array UInt64) : Assertion Unit :=
  fun continuation => match continuation with
    | .Fallthrough final frame =>
        wp module_ [.localGet 14] (publicPost input) final
          { frame with values := [] } env
    | .Break 0 final frame =>
        wp module_ [.localGet 14] (publicPost input) final
          { frame with values := [] } env
    | .Break (index + 1) final frame =>
        publicPost input (.Break index final frame)
    | other => publicPost input other

theorem pairPost_conseq
    (module_ : Wasm.Module) (env : HostEnv Unit) (input : Array UInt64)
    (first second : UInt64)
    (hExpected : FormalSpec.expected input = #[first, second]) :
    pairPost first second ⇛ resultContinuation module_ env input := by
  intro continuation hPair
  cases continuation <;> simp only [pairPost] at hPair
  rename_i final frame
  rcases hPair with
    ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
      hOutputLocal, hOutput⟩
  have hOutputGet : frame.locals[13] = .i64 outputPtr := by
    have h := hOutputLocal
    rw [List.getElem?_eq_getElem (by omega)] at h
    exact Option.some.inj h
  simp only [resultContinuation]
  wp_alloc_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
  simp only [publicPost]
  refine ⟨outputPtr, rfl, ?_⟩
  change Project.ProofKit.UInt64Array.At final outputPtr
    (FormalSpec.expected input)
  rw [hExpected]
  exact hOutput

theorem artifact_behavior :
    FormalSpec.ArtifactSpec LeanExeGen.GeneratedReb06c2a75684e92c.«module» := by
  refine ⟨0, rfl, ?_⟩
  intro env initial inputPtr input hInput
  rcases hInput with
    ⟨hArray, heapTop, allocs, retains, releases, frees, hGlobals,
      hInputBelow, hFit32Expected, hFitMemoryExpected, hPages⟩
  change Project.ProofKit.UInt64Array.At initial inputPtr input at hArray
  have hLengthRead := hArray.lengthRead
  have hLengthBound := hArray.lengthBound
  have hInputAddress := hArray.pointerAddress_eq
  have hLengthBound' : inputPtr.toNat % 4294967296 + 8 ≤
      initial.mem.pages * 65536 := by
    simpa [Project.ProofKit.Memory.toUInt32_toNat] using hLengthBound
  have hEncoded21 : UInt64.ofNat input.size = 21 ↔ input.size = 21 := by
    simpa using hArray.encodedSize_eq (size := 21) (by
      norm_num [UInt64.size])
  have hHeapTop : initial.globals.globals[0]? = some (.i64 heapTop) := by
    simp [hGlobals]
  have hFreeList : initial.globals.globals[1]? = some (.i64 0) := by
    simp [hGlobals]
  have hAllocs : initial.globals.globals[2]? = some (.i64 allocs) := by
    simp [hGlobals]
  by_cases hSize : input.size = 21
  · have hElement (index : Nat) (hIndex : index < input.size) :
        (inputPtr.toNat + (index + 1) * 8) % 4294967296 + 8 ≤
            initial.mem.pages * 65536 ∧
          initial.mem.read64
              (UInt32.ofNat ((inputPtr.toNat + 8 * (index + 1)) %
                4294967296)) =
            input[index] := by
      have hRead := hArray.elementRead index hIndex
      have hBound := hArray.elementBound index hIndex
      have hAddress := hArray.elementAddress_eq index hIndex
      constructor
      · have hBound' :
            (UInt32.ofNat ((inputPtr.toNat + 8 * (index + 1)) %
              4294967296)).toNat + 8 ≤ initial.mem.pages * 65536 := by
          rw [hAddress]
          exact hBound
        simpa [Nat.mul_comm] using hBound'
      · rw [hAddress]
        exact hRead
    have hIndex0 : 0 < input.size := by omega
    have hRead0 := hArray.elementRead 0 hIndex0
    have hBound0 := hArray.elementBound 0 hIndex0
    have hAddress0 := hArray.elementAddress_eq 0 hIndex0
    have hBound0' : (inputPtr.toNat + (0 + 1) * 8) % 4294967296 + 8 ≤
        initial.mem.pages * 65536 := by
      have hBound :
          (UInt32.ofNat ((inputPtr.toNat + 8 * (0 + 1)) %
            4294967296)).toNat + 8 ≤ initial.mem.pages * 65536 := by
        rw [hAddress0]
        exact hBound0
      simpa [Nat.mul_comm] using hBound
    have hGeneratedAddress0 :
        UInt32.ofNat ((inputPtr.toNat + 8) % 4294967296) =
          inputPtr.toUInt32 + 8 := by
      apply UInt32.toNat.inj
      simp
    have hRead0' : initial.mem.read64 (inputPtr.toUInt32 + 8) = input[0] := by
      rw [← hGeneratedAddress0, hAddress0]
      exact hRead0
    apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
    unfold func0Def func0
    wp_alloc_run24 [hLengthRead, hLengthBound, hInputAddress, hEncoded21,
      hSize]
    refine ⟨hLengthBound', ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_alloc_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_alloc_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_alloc_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_alloc_run24 [hLengthRead, hLengthBound, hInputAddress, hSize]
    refine ⟨hLengthBound', ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hSize])]
    wp_alloc_run24 [hLengthRead, hInputAddress, hRead0, hRead0', hBound0,
      hAddress0, hSize]
    refine ⟨hBound0', ?_⟩
    have hElement1 := hElement 1 (by omega)
    refine ⟨hLengthBound', ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp [hLengthRead, hInputAddress, hSize])]
    wp_alloc_run24 [hLengthRead, hInputAddress, hElement1.2, hSize]
    refine ⟨hElement1.1, ?_⟩
    by_cases hKey1 : input[1] = input[0]
    · refine wp_iff_cons rfl ?_
      rw [if_pos (by simp [hKey1])]
      wp_alloc_run24 []
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp)]
      have hExpected : FormalSpec.expected input = #[input[2], 1] := by
        simp [FormalSpec.expected, hSize, hKey1]
      change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
        (inputResultProgram 2 3) _ initial _ env
      apply Wasm.wp.conseq (Q := pairPost input[2] 1)
      · intro continuation hPair
        cases continuation <;> simp only [pairPost] at hPair
        rename_i final frame'
        rcases hPair with
          ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
            hOutputLocal, hOutput⟩
        have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
          have h := hOutputLocal
          rw [List.getElem?_eq_getElem (by omega)] at h
          exact Option.some.inj h
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        wp_alloc_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
        change Project.ProofKit.UInt64Array.At final outputPtr
          (FormalSpec.expected input)
        rw [hExpected]
        exact hOutput
      · have hFit := hFitMemoryExpected
        rw [hExpected] at hFit
        exact inputResultProgram_spec
          LeanExeGen.GeneratedReb06c2a75684e92c.«module» env initial _
          heapTop allocs inputPtr input 2 3 rfl rfl rfl (by decide)
          (by decide) hArray (by omega) hInputBelow (by simpa using hFit)
          hPages rfl hHeapTop hFreeList hAllocs
    · refine wp_iff_cons rfl ?_
      rw [if_neg (by simp [hKey1])]
      wp_alloc_run24 []
      refine wp_iff_cons rfl ?_
      rw [if_neg (by simp)]
      apply Wasm.wp.conseq (Q := fallthroughPost
        LeanExeGen.GeneratedReb06c2a75684e92c.«module» env input)
      · intro continuation hFallthrough
        cases continuation <;> simp only [fallthroughPost] at hFallthrough
        rename_i final frame'
        simpa only [List.take_zero, List.drop_zero, List.nil_append,
          wp_simp, publicPost, Wasm.Locals.get, List.take,
          List.cons.injEq, and_true] using hFallthrough
      have hElement3 := hElement 3 (by omega)
      wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
      rw [if_neg (Nat.not_lt.mpr hLengthBound')]
      refine wp_iff_cons rfl ?_
      rw [if_pos (by simp [hSize])]
      wp_alloc_run24 [hLengthRead, hInputAddress, hElement3.2, hSize]
      rw [if_neg (Nat.not_lt.mpr hElement3.1)]
      by_cases hKey3 : input[3] = input[0]
      · refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hKey3])]
        wp_alloc_run24 []
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        have hExpected : FormalSpec.expected input = #[input[4], 1] := by
          simp [FormalSpec.expected, hSize, hKey1, hKey3]
        change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
          (inputResultProgram 4 4) _ initial _ env
        apply Wasm.wp.conseq (Q := pairPost input[4] 1)
        · intro continuation hPair
          cases continuation <;> simp only [pairPost] at hPair
          rename_i final frame'
          rcases hPair with
            ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
              hOutputLocal, hOutput⟩
          have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
            have h := hOutputLocal
            rw [List.getElem?_eq_getElem (by omega)] at h
            exact Option.some.inj h
          simp only [List.take_zero, List.drop_zero, List.nil_append]
          wp_alloc_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
          simp only [fallthroughPost]
          wp_alloc_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
          simp only [publicPost]
          refine ⟨outputPtr, rfl, ?_⟩
          change Project.ProofKit.UInt64Array.At final outputPtr
            (FormalSpec.expected input)
          rw [hExpected]
          exact hOutput
        · have hFit := hFitMemoryExpected
          rw [hExpected] at hFit
          exact inputResultProgram_spec
            LeanExeGen.GeneratedReb06c2a75684e92c.«module» env initial _
            heapTop allocs inputPtr input 4 4 rfl rfl rfl (by decide)
            (by decide) hArray (by omega) hInputBelow (by simpa using hFit)
            hPages rfl hHeapTop hFreeList hAllocs
      · refine wp_iff_cons rfl ?_
        rw [if_neg (by simp [hKey3])]
        wp_alloc_run24 []
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        apply Wasm.wp.conseq (Q := fallthroughPost
          LeanExeGen.GeneratedReb06c2a75684e92c.«module» env input)
        · intro continuation hFallthrough
          cases continuation
          case Fallthrough final frame' =>
            simpa only [List.take_zero, List.drop_zero, List.nil_append,
              wp_simp, fallthroughPost] using hFallthrough
          all_goals simp only [fallthroughPost] at hFallthrough
        have hElement5 := hElement 5 (by omega)
        wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
        rw [if_neg (Nat.not_lt.mpr hLengthBound')]
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp [hSize])]
        wp_alloc_run24 [hLengthRead, hInputAddress, hElement5.2, hSize]
        rw [if_neg (Nat.not_lt.mpr hElement5.1)]
        by_cases hKey5 : input[5] = input[0]
        · refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hKey5])]
          wp_alloc_run24 []
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp)]
          have hExpected : FormalSpec.expected input = #[input[6], 1] := by
            simp [FormalSpec.expected, hSize, hKey1, hKey3, hKey5]
          change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
            (inputResultProgram 6 5) _ initial _ env
          apply Wasm.wp.conseq (Q := pairPost input[6] 1)
          · intro continuation hPair
            cases continuation <;> simp only [pairPost] at hPair
            rename_i final frame'
            rcases hPair with
              ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                hOutputLocal, hOutput⟩
            have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
              have h := hOutputLocal
              rw [List.getElem?_eq_getElem (by omega)] at h
              exact Option.some.inj h
            simp only [List.take_zero, List.drop_zero, List.nil_append]
            wp_alloc_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
            simp only [fallthroughPost]
            wp_alloc_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
            simp only [publicPost]
            refine ⟨outputPtr, rfl, ?_⟩
            change Project.ProofKit.UInt64Array.At final outputPtr
              (FormalSpec.expected input)
            rw [hExpected]
            exact hOutput
          · have hFit := hFitMemoryExpected
            rw [hExpected] at hFit
            exact inputResultProgram_spec
              LeanExeGen.GeneratedReb06c2a75684e92c.«module» env initial _
              heapTop allocs inputPtr input 6 5 rfl rfl rfl (by decide)
              (by decide) hArray (by omega) hInputBelow (by simpa using hFit)
              hPages rfl hHeapTop hFreeList hAllocs
        · refine wp_iff_cons rfl ?_
          rw [if_neg (by simp [hKey5])]
          wp_alloc_run24 []
          refine wp_iff_cons rfl ?_
          rw [if_neg (by simp)]
          apply Wasm.wp.conseq (Q := fallthroughPost
            LeanExeGen.GeneratedReb06c2a75684e92c.«module» env input)
          · intro continuation hFallthrough
            cases continuation
            case Fallthrough final frame' =>
              simpa only [List.take_zero, List.drop_zero, List.nil_append,
                wp_simp, fallthroughPost] using hFallthrough
            all_goals simp only [fallthroughPost] at hFallthrough
          have hElement7 := hElement 7 (by omega)
          wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
          rw [if_neg (Nat.not_lt.mpr hLengthBound')]
          refine wp_iff_cons rfl ?_
          rw [if_pos (by simp [hSize])]
          wp_alloc_run24 [hLengthRead, hInputAddress, hElement7.2, hSize]
          rw [if_neg (Nat.not_lt.mpr hElement7.1)]
          by_cases hKey7 : input[7] = input[0]
          · refine wp_iff_cons rfl ?_
            rw [if_pos (by simp [hKey7])]
            wp_alloc_run24 []
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp)]
            have hExpected : FormalSpec.expected input = #[input[8], 1] := by
              simp [FormalSpec.expected, hSize, hKey1, hKey3, hKey5, hKey7]
            change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
              (inputResultProgram 8 6) _ initial _ env
            apply Wasm.wp.conseq (Q := pairPost input[8] 1)
            · intro continuation hPair
              cases continuation <;> simp only [pairPost] at hPair
              rename_i final frame'
              rcases hPair with
                ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                  hOutputLocal, hOutput⟩
              have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                have h := hOutputLocal
                rw [List.getElem?_eq_getElem (by omega)] at h
                exact Option.some.inj h
              simp only [List.take_zero, List.drop_zero, List.nil_append]
              wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                hOutputGet]
              simp only [fallthroughPost]
              wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                hOutputGet]
              simp only [publicPost]
              refine ⟨outputPtr, rfl, ?_⟩
              change Project.ProofKit.UInt64Array.At final outputPtr
                (FormalSpec.expected input)
              rw [hExpected]
              exact hOutput
            · have hFit := hFitMemoryExpected
              rw [hExpected] at hFit
              exact inputResultProgram_spec
                LeanExeGen.GeneratedReb06c2a75684e92c.«module» env initial _
                heapTop allocs inputPtr input 8 6 rfl rfl rfl (by decide)
                (by decide) hArray (by omega) hInputBelow
                (by simpa using hFit) hPages rfl hHeapTop hFreeList hAllocs
          · refine wp_iff_cons rfl ?_
            rw [if_neg (by simp [hKey7])]
            wp_alloc_run24 []
            refine wp_iff_cons rfl ?_
            rw [if_neg (by simp)]
            apply Wasm.wp.conseq (Q := fallthroughPost
              LeanExeGen.GeneratedReb06c2a75684e92c.«module» env input)
            · intro continuation hFallthrough
              cases continuation
              case Fallthrough final frame' =>
                simpa only [List.take_zero, List.drop_zero, List.nil_append,
                  wp_simp, fallthroughPost] using hFallthrough
              all_goals simp only [fallthroughPost] at hFallthrough
            have hElement9 := hElement 9 (by omega)
            wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
            rw [if_neg (Nat.not_lt.mpr hLengthBound')]
            refine wp_iff_cons rfl ?_
            rw [if_pos (by simp [hSize])]
            wp_alloc_run24 [hLengthRead, hInputAddress, hElement9.2, hSize]
            rw [if_neg (Nat.not_lt.mpr hElement9.1)]
            by_cases hKey9 : input[9] = input[0]
            · refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hKey9])]
              wp_alloc_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp)]
              have hExpected : FormalSpec.expected input = #[input[10], 1] := by
                simp [FormalSpec.expected, hSize, hKey1, hKey3, hKey5,
                  hKey7, hKey9]
              change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                (inputResultProgram 10 7) _ initial _ env
              apply Wasm.wp.conseq (Q := pairPost input[10] 1)
              · intro continuation hPair
                cases continuation <;> simp only [pairPost] at hPair
                rename_i final frame'
                rcases hPair with
                  ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                    hOutputLocal, hOutput⟩
                have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                  have h := hOutputLocal
                  rw [List.getElem?_eq_getElem (by omega)] at h
                  exact Option.some.inj h
                simp only [List.take_zero, List.drop_zero, List.nil_append]
                wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                  hOutputGet]
                simp only [fallthroughPost]
                wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                  hOutputGet]
                simp only [publicPost]
                refine ⟨outputPtr, rfl, ?_⟩
                change Project.ProofKit.UInt64Array.At final outputPtr
                  (FormalSpec.expected input)
                rw [hExpected]
                exact hOutput
              · have hFit := hFitMemoryExpected
                rw [hExpected] at hFit
                exact inputResultProgram_spec
                  LeanExeGen.GeneratedReb06c2a75684e92c.«module» env initial _
                  heapTop allocs inputPtr input 10 7 rfl rfl rfl (by decide)
                  (by decide) hArray (by omega) hInputBelow
                  (by simpa using hFit) hPages rfl hHeapTop hFreeList hAllocs
            · refine wp_iff_cons rfl ?_
              rw [if_neg (by simp [hKey9])]
              wp_alloc_run24 []
              refine wp_iff_cons rfl ?_
              rw [if_neg (by simp)]
              apply Wasm.wp.conseq (Q := fallthroughPost
                LeanExeGen.GeneratedReb06c2a75684e92c.«module» env input)
              · intro continuation hFallthrough
                cases continuation
                case Fallthrough final frame' =>
                  simpa only [List.take_zero, List.drop_zero, List.nil_append,
                    wp_simp, fallthroughPost] using hFallthrough
                all_goals simp only [fallthroughPost] at hFallthrough
              have hElement11 := hElement 11 (by omega)
              wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
              rw [if_neg (Nat.not_lt.mpr hLengthBound')]
              refine wp_iff_cons rfl ?_
              rw [if_pos (by simp [hSize])]
              wp_alloc_run24 [hLengthRead, hInputAddress, hElement11.2,
                hSize]
              rw [if_neg (Nat.not_lt.mpr hElement11.1)]
              by_cases hKey11 : input[11] = input[0]
              · refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hKey11])]
                wp_alloc_run24 []
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp)]
                have hExpected :
                    FormalSpec.expected input = #[input[12], 1] := by
                  simp [FormalSpec.expected, hSize, hKey1, hKey3, hKey5,
                    hKey7, hKey9, hKey11]
                change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                  (inputResultProgram 12 8) _ initial _ env
                apply Wasm.wp.conseq (Q := pairPost input[12] 1)
                · intro continuation hPair
                  cases continuation <;> simp only [pairPost] at hPair
                  rename_i final frame'
                  rcases hPair with
                    ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                      hOutputLocal, hOutput⟩
                  have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
                    have h := hOutputLocal
                    rw [List.getElem?_eq_getElem (by omega)] at h
                    exact Option.some.inj h
                  simp only [List.take_zero, List.drop_zero, List.nil_append]
                  wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                    hOutputGet]
                  simp only [fallthroughPost]
                  wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                    hOutputGet]
                  simp only [publicPost]
                  refine ⟨outputPtr, rfl, ?_⟩
                  change Project.ProofKit.UInt64Array.At final outputPtr
                    (FormalSpec.expected input)
                  rw [hExpected]
                  exact hOutput
                · have hFit := hFitMemoryExpected
                  rw [hExpected] at hFit
                  exact inputResultProgram_spec
                    LeanExeGen.GeneratedReb06c2a75684e92c.«module» env
                    initial _ heapTop allocs inputPtr input 12 8 rfl rfl rfl
                    (by decide) (by decide) hArray (by omega) hInputBelow
                    (by simpa using hFit) hPages rfl hHeapTop hFreeList hAllocs
              · refine wp_iff_cons rfl ?_
                rw [if_neg (by simp [hKey11])]
                wp_alloc_run24 []
                refine wp_iff_cons rfl ?_
                rw [if_neg (by simp)]
                apply Wasm.wp.conseq (Q := fallthroughPost
                  LeanExeGen.GeneratedReb06c2a75684e92c.«module» env input)
                · intro continuation hFallthrough
                  cases continuation
                  case Fallthrough final frame' =>
                    simpa only [List.take_zero, List.drop_zero,
                      List.nil_append, wp_simp, fallthroughPost]
                      using hFallthrough
                  all_goals simp only [fallthroughPost] at hFallthrough
                have hElement13 := hElement 13 (by omega)
                wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
                rw [if_neg (Nat.not_lt.mpr hLengthBound')]
                refine wp_iff_cons rfl ?_
                rw [if_pos (by simp [hSize])]
                wp_alloc_run24 [hLengthRead, hInputAddress, hElement13.2,
                  hSize]
                rw [if_neg (Nat.not_lt.mpr hElement13.1)]
                by_cases hKey13 : input[13] = input[0]
                · refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp [hKey13])]
                  wp_alloc_run24 []
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp)]
                  have hExpected :
                      FormalSpec.expected input = #[input[14], 1] := by
                    simp [FormalSpec.expected, hSize, hKey1, hKey3, hKey5,
                      hKey7, hKey9, hKey11, hKey13]
                  change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                    (inputResultProgram 14 9) _ initial _ env
                  apply Wasm.wp.conseq (Q := pairPost input[14] 1)
                  · intro continuation hPair
                    cases continuation <;> simp only [pairPost] at hPair
                    rename_i final frame'
                    rcases hPair with
                      ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                        hOutputLocal, hOutput⟩
                    have hOutputGet :
                        frame'.locals[13] = .i64 outputPtr := by
                      have h := hOutputLocal
                      rw [List.getElem?_eq_getElem (by omega)] at h
                      exact Option.some.inj h
                    simp only [List.take_zero, List.drop_zero,
                      List.nil_append]
                    wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                      hOutputGet]
                    simp only [fallthroughPost]
                    wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                      hOutputGet]
                    simp only [publicPost]
                    refine ⟨outputPtr, rfl, ?_⟩
                    change Project.ProofKit.UInt64Array.At final outputPtr
                      (FormalSpec.expected input)
                    rw [hExpected]
                    exact hOutput
                  · have hFit := hFitMemoryExpected
                    rw [hExpected] at hFit
                    exact inputResultProgram_spec
                      LeanExeGen.GeneratedReb06c2a75684e92c.«module» env
                      initial _ heapTop allocs inputPtr input 14 9 rfl rfl rfl
                      (by decide) (by decide) hArray (by omega) hInputBelow
                      (by simpa using hFit) hPages rfl hHeapTop hFreeList
                      hAllocs
                · refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp [hKey13])]
                  wp_alloc_run24 []
                  refine wp_iff_cons rfl ?_
                  rw [if_neg (by simp)]
                  apply Wasm.wp.conseq (Q := fallthroughPost
                    LeanExeGen.GeneratedReb06c2a75684e92c.«module» env input)
                  · intro continuation hFallthrough
                    cases continuation
                    case Fallthrough final frame' =>
                      simpa only [List.take_zero, List.drop_zero,
                        List.nil_append, wp_simp, fallthroughPost]
                        using hFallthrough
                    all_goals simp only [fallthroughPost] at hFallthrough
                  have hElement15 := hElement 15 (by omega)
                  wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
                  rw [if_neg (Nat.not_lt.mpr hLengthBound')]
                  refine wp_iff_cons rfl ?_
                  rw [if_pos (by simp [hSize])]
                  wp_alloc_run24 [hLengthRead, hInputAddress, hElement15.2,
                    hSize]
                  rw [if_neg (Nat.not_lt.mpr hElement15.1)]
                  by_cases hKey15 : input[15] = input[0]
                  · refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hKey15])]
                    wp_alloc_run24 []
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp)]
                    have hExpected :
                        FormalSpec.expected input = #[input[16], 1] := by
                      simp [FormalSpec.expected, hSize, hKey1, hKey3, hKey5,
                        hKey7, hKey9, hKey11, hKey13, hKey15]
                    change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                      (inputResultProgram 16 10) _ initial _ env
                    apply Wasm.wp.conseq (Q := pairPost input[16] 1)
                    · intro continuation hPair
                      cases continuation <;> simp only [pairPost] at hPair
                      rename_i final frame'
                      rcases hPair with
                        ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                          hOutputLocal, hOutput⟩
                      have hOutputGet :
                          frame'.locals[13] = .i64 outputPtr := by
                        have h := hOutputLocal
                        rw [List.getElem?_eq_getElem (by omega)] at h
                        exact Option.some.inj h
                      simp only [List.take_zero, List.drop_zero,
                        List.nil_append]
                      wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                        hOutputGet]
                      simp only [fallthroughPost]
                      wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                        hOutputGet]
                      simp only [publicPost]
                      refine ⟨outputPtr, rfl, ?_⟩
                      change Project.ProofKit.UInt64Array.At final outputPtr
                        (FormalSpec.expected input)
                      rw [hExpected]
                      exact hOutput
                    · have hFit := hFitMemoryExpected
                      rw [hExpected] at hFit
                      exact inputResultProgram_spec
                        LeanExeGen.GeneratedReb06c2a75684e92c.«module» env
                        initial _ heapTop allocs inputPtr input 16 10 rfl rfl
                        rfl (by decide) (by decide) hArray (by omega)
                        hInputBelow (by simpa using hFit) hPages rfl hHeapTop
                        hFreeList hAllocs
                  · refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp [hKey15])]
                    wp_alloc_run24 []
                    refine wp_iff_cons rfl ?_
                    rw [if_neg (by simp)]
                    apply Wasm.wp.conseq (Q := fallthroughPost
                      LeanExeGen.GeneratedReb06c2a75684e92c.«module» env input)
                    · intro continuation hFallthrough
                      cases continuation
                      case Fallthrough final frame' =>
                        simpa only [List.take_zero, List.drop_zero,
                          List.nil_append, wp_simp, fallthroughPost]
                          using hFallthrough
                      all_goals simp only [fallthroughPost] at hFallthrough
                    have hElement17 := hElement 17 (by omega)
                    wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
                    rw [if_neg (Nat.not_lt.mpr hLengthBound')]
                    refine wp_iff_cons rfl ?_
                    rw [if_pos (by simp [hSize])]
                    wp_alloc_run24 [hLengthRead, hInputAddress, hElement17.2,
                      hSize]
                    rw [if_neg (Nat.not_lt.mpr hElement17.1)]
                    by_cases hKey17 : input[17] = input[0]
                    · refine wp_iff_cons rfl ?_
                      rw [if_pos (by simp [hKey17])]
                      wp_alloc_run24 []
                      refine wp_iff_cons rfl ?_
                      rw [if_pos (by simp)]
                      have hExpected :
                          FormalSpec.expected input = #[input[18], 1] := by
                        simp [FormalSpec.expected, hSize, hKey1, hKey3,
                          hKey5, hKey7, hKey9, hKey11, hKey13, hKey15,
                          hKey17]
                      change wp
                        LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                        (inputResultProgram 18 11) _ initial _ env
                      apply Wasm.wp.conseq (Q := pairPost input[18] 1)
                      · intro continuation hPair
                        cases continuation <;> simp only [pairPost] at hPair
                        rename_i final frame'
                        rcases hPair with
                          ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
                            hOutputLocal, hOutput⟩
                        have hOutputGet :
                            frame'.locals[13] = .i64 outputPtr := by
                          have h := hOutputLocal
                          rw [List.getElem?_eq_getElem (by omega)] at h
                          exact Option.some.inj h
                        simp only [List.take_zero, List.drop_zero,
                          List.nil_append]
                        wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                          hOutputGet]
                        simp only [fallthroughPost]
                        wp_alloc_run24 [hValues, hParamsLength, hLocalsLength,
                          hOutputGet]
                        simp only [publicPost]
                        refine ⟨outputPtr, rfl, ?_⟩
                        change Project.ProofKit.UInt64Array.At final outputPtr
                          (FormalSpec.expected input)
                        rw [hExpected]
                        exact hOutput
                      · have hFit := hFitMemoryExpected
                        rw [hExpected] at hFit
                        exact inputResultProgram_spec
                          LeanExeGen.GeneratedReb06c2a75684e92c.«module» env
                          initial _ heapTop allocs inputPtr input 18 11 rfl rfl
                          rfl (by decide) (by decide) hArray (by omega)
                          hInputBelow (by simpa using hFit) hPages rfl hHeapTop
                          hFreeList hAllocs
                    · refine wp_iff_cons rfl ?_
                      rw [if_neg (by simp [hKey17])]
                      wp_alloc_run24 []
                      refine wp_iff_cons rfl ?_
                      rw [if_neg (by simp)]
                      apply Wasm.wp.conseq (Q := fallthroughPost
                        LeanExeGen.GeneratedReb06c2a75684e92c.«module» env
                        input)
                      · intro continuation hFallthrough
                        cases continuation
                        case Fallthrough final frame' =>
                          simpa only [List.take_zero, List.drop_zero,
                            List.nil_append, wp_simp, fallthroughPost]
                            using hFallthrough
                        all_goals
                          simp only [fallthroughPost] at hFallthrough
                      have hElement19 := hElement 19 (by omega)
                      wp_alloc_run24 [hLengthRead, hInputAddress, hSize]
                      rw [if_neg (Nat.not_lt.mpr hLengthBound')]
                      refine wp_iff_cons rfl ?_
                      rw [if_pos (by simp [hSize])]
                      wp_alloc_run24 [hLengthRead, hInputAddress,
                        hElement19.2, hSize]
                      rw [if_neg (Nat.not_lt.mpr hElement19.1)]
                      by_cases hKey19 : input[19] = input[0]
                      · refine wp_iff_cons rfl ?_
                        rw [if_pos (by simp [hKey19])]
                        wp_alloc_run24 []
                        refine wp_iff_cons rfl ?_
                        rw [if_pos (by simp)]
                        have hExpected :
                            FormalSpec.expected input = #[input[20], 1] := by
                          simp [FormalSpec.expected, hSize, hKey1, hKey3,
                            hKey5, hKey7, hKey9, hKey11, hKey13, hKey15,
                            hKey17, hKey19]
                        change wp
                          LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                          (inputResultProgram 20 12) _ initial _ env
                        apply Wasm.wp.conseq (Q := pairPost input[20] 1)
                        · intro continuation hPair
                          cases continuation <;>
                            simp only [pairPost] at hPair
                          rename_i final frame'
                          rcases hPair with
                            ⟨outputPtr, hValues, hParamsLength,
                              hLocalsLength, hOutputLocal, hOutput⟩
                          have hOutputGet :
                              frame'.locals[13] = .i64 outputPtr := by
                            have h := hOutputLocal
                            rw [List.getElem?_eq_getElem (by omega)] at h
                            exact Option.some.inj h
                          simp only [List.take_zero, List.drop_zero,
                            List.nil_append]
                          wp_alloc_run24 [hValues, hParamsLength,
                            hLocalsLength, hOutputGet]
                          simp only [fallthroughPost]
                          wp_alloc_run24 [hValues, hParamsLength,
                            hLocalsLength, hOutputGet]
                          simp only [publicPost]
                          refine ⟨outputPtr, rfl, ?_⟩
                          change Project.ProofKit.UInt64Array.At final
                            outputPtr (FormalSpec.expected input)
                          rw [hExpected]
                          exact hOutput
                        · have hFit := hFitMemoryExpected
                          rw [hExpected] at hFit
                          exact inputResultProgram_spec
                            LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                            env initial _ heapTop allocs inputPtr input 20 12
                            rfl rfl rfl (by decide) (by decide) hArray
                            (by omega) hInputBelow (by simpa using hFit)
                            hPages rfl hHeapTop hFreeList hAllocs
                      · refine wp_iff_cons rfl ?_
                        rw [if_neg (by simp [hKey19])]
                        wp_alloc_run24 []
                        refine wp_iff_cons rfl ?_
                        rw [if_neg (by simp)]
                        have hExpected :
                            FormalSpec.expected input = #[0, 0] := by
                          simp [FormalSpec.expected, hSize, hKey1, hKey3,
                            hKey5, hKey7, hKey9, hKey11, hKey13, hKey15,
                            hKey17, hKey19]
                        change wp
                          LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                          (constResultProgram 0 0 13) _ initial _ env
                        apply Wasm.wp.conseq (Q := pairPost 0 0)
                        · intro continuation hPair
                          cases continuation <;>
                            simp only [pairPost] at hPair
                          rename_i final frame'
                          rcases hPair with
                            ⟨outputPtr, hValues, hParamsLength,
                              hLocalsLength, hOutputLocal, hOutput⟩
                          have hOutputGet :
                              frame'.locals[13] = .i64 outputPtr := by
                            have h := hOutputLocal
                            rw [List.getElem?_eq_getElem (by omega)] at h
                            exact Option.some.inj h
                          simp only [List.take_zero, List.drop_zero,
                            List.nil_append]
                          wp_alloc_run24 [hValues, hParamsLength,
                            hLocalsLength, hOutputGet]
                          simp only [fallthroughPost]
                          wp_alloc_run24 [hValues, hParamsLength,
                            hLocalsLength, hOutputGet]
                          simp only [publicPost]
                          refine ⟨outputPtr, rfl, ?_⟩
                          change Project.ProofKit.UInt64Array.At final
                            outputPtr (FormalSpec.expected input)
                          rw [hExpected]
                          exact hOutput
                        · have hFit := hFitMemoryExpected
                          rw [hExpected] at hFit
                          exact constResultProgram_spec
                            LeanExeGen.GeneratedReb06c2a75684e92c.«module»
                            env initial _ heapTop allocs 0 0 13 rfl rfl rfl
                            (by decide) (by decide) (by simpa using hFit)
                            hPages rfl hHeapTop hFreeList hAllocs
  · apply Wasm.TerminatesWith.of_wp_entry_for (f := func0Def) rfl
    unfold func0Def func0
    wp_alloc_run24 [hLengthRead, hLengthBound, hInputAddress, hEncoded21,
      hSize]
    refine ⟨hLengthBound', ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_alloc_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_alloc_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_alloc_run24 []
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    change wp LeanExeGen.GeneratedReb06c2a75684e92c.«module»
      (constResultProgram 0 0 1) _ initial _ env
    apply Wasm.wp.conseq (Q := pairPost 0 0)
    · intro continuation hPair
      cases continuation <;> simp only [pairPost] at hPair
      rename_i final frame'
      rcases hPair with
        ⟨outputPtr, hValues, hParamsLength, hLocalsLength,
          hOutputLocal, hOutput⟩
      have hOutputGet : frame'.locals[13] = .i64 outputPtr := by
        have h := hOutputLocal
        rw [List.getElem?_eq_getElem (by omega)] at h
        exact Option.some.inj h
      simp only [List.take_zero, List.drop_zero, List.nil_append]
      wp_alloc_run24 [hValues, hParamsLength, hLocalsLength, hOutputGet]
      change Project.ProofKit.UInt64Array.At final outputPtr
        (FormalSpec.expected input)
      simpa [FormalSpec.expected, hSize] using hOutput
    · apply constResultProgram_spec
        LeanExeGen.GeneratedReb06c2a75684e92c.«module» env initial _
        heapTop allocs 0 0 1
      · rfl
      · rfl
      · rfl
      · decide
      · decide
      · have hExpected : FormalSpec.expected input = #[0, 0] := by
          simp [FormalSpec.expected, hSize]
        rw [hExpected] at hFitMemoryExpected
        simpa using hFitMemoryExpected
      · exact hPages
      · rfl
      · exact hHeapTop
      · exact hFreeList
      · exact hAllocs

end LeanExeGen.GeneratedReb06c2a75684e92c.Behavior
