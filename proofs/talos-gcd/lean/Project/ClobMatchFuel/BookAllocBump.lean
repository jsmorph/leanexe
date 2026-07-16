import Project.ClobMatchFuel.BookAllocFit
import Project.FixedArrayAllocation

namespace Project.ClobMatchFuel.BookAllocBump

open Wasm Project.Common Project.Runtime Project.Clob
  Project.ClobMatchFuel

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_bump" "(" hParams:term "," hLocals:term "," hValues:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues)])

def bookAllocBumpProg : Wasm.Program :=
  [
  .localGet 81,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localGet 76,
    .addI64,
    .localSet 79,
    .localGet 79,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 79,
    .constI64 (1 : UInt64),
    .subI64,
    .constI64 (65536 : UInt64),
    .divUI64,
    .constI64 (1 : UInt64),
    .addI64,
    .localSet 80,
    .memorySize,
    .extendUI32,
    .localGet 80,
    .ltUI64,
    .iff 0 0 [
      .localGet 80,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const (4294967295 : UInt32),
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localSet 81,
    .localGet 79,
    .globalSet 0,
    .localGet 81,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 81,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 81,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 76,
    .store64 (0 : UInt32),
    .localGet 81,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (2 : UInt64),
    .store64 (0 : UInt32),
    .localGet 81,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5 : UInt64),
    .store64 (0 : UInt32),
    .localGet 81,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32)
  ] []
]

def fixedArrayAllocBumpStore (st : Store Unit) (g0 need stride : UInt64) :
    Store Unit :=
  { st with
    globals := { globals :=
      (st.globals.globals.set 0 (.i64 (g0 + 48 + need))) }
    mem := fixedArrayHeaderMem st.mem g0 need stride }

abbrev bookAllocBumpStore (st : Store Unit) (g0 need : UInt64) :
    Store Unit :=
  fixedArrayAllocBumpStore st g0 need 5

set_option Elab.async false in
theorem bookAllocBumpProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (g0 need previous capacity next : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hNeed8 : 8 ≤ need.toNat)
    (htop : (g0 + 48 + need).toNat =
      g0.toNat + 48 + need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hFit : g0.toNat + 48 + need.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q (bookAllocBumpStore st g0 need)
      (BookAllocSearch.bookAllocSearchFrame base need previous 0
        (g0 + 48 + need)
        ((g0 + 48 + need - 1) / 65536 + 1) (g0 + 48)) env) :
    wp «module» (bookAllocBumpProg ++ rest) Q st
      (BookAllocSearch.bookAllocSearchFrame base need previous 0
        capacity next 0) env := by
  simp only [bookAllocBumpProg, List.cons_append, List.nil_append,
    BookAllocSearch.bookAllocSearchFrame]
  wp_run_bump (hParams, hLocals, hValues)
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run_bump (hParams, hLocals, hValues)
  simp only [hg0]
  have hnoWrap : ¬ g0 + 48 + need < g0 := by
    rw [UInt64.lt_iff_toNat_lt, htop]
    omega
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hnoWrap])]
  wp_run_bump (hParams, hLocals, hValues)
  have htopSub :
      (g0 + 48 + need - 1).toNat =
        g0.toNat + 48 + need.toNat - 1 := by
    rw [toNat_sub_le _ _ (by rw [htop]; simp; omega), htop]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
  have hpagesNeeded :
      ((g0 + 48 + need - 1) / 65536 + 1).toNat =
        (g0.toNat + 48 + need.toNat - 1) / 65536 + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_div, htopSub]
    have h65536 : (65536 : UInt64).toNat = 65536 := rfl
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h65536, h1]
    omega
  have hmemorySize :
      ((UInt32.ofNat st.mem.pages).toUInt64).toNat = st.mem.pages := by
    have hlt : st.mem.pages < UInt32.size := by
      have hs : UInt32.size = 4294967296 := rfl
      omega
    have hnat : (UInt32.ofNat st.mem.pages).toNat = st.mem.pages :=
      UInt32.toNat_ofNat_of_lt' hlt
    simp [hnat]
  have hnoGrow : ¬
      ((UInt32.ofNat st.mem.pages).toUInt64 <
        (g0 + 48 + need - 1) / 65536 + 1) := by
    rw [UInt64.lt_iff_toNat_lt, hmemorySize, hpagesNeeded]
    omega
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hnoGrow])]
  wp_run_bump (hParams, hLocals, hValues)
  simp only [hg0]
  try wp_run_bump (hParams, hLocals, hValues)
  try simp
  have hsub (offset : UInt64) (hOffset : offset.toNat ≤ 48) :
      (g0 + 48 - offset).toNat =
        g0.toNat + 48 - offset.toNat := by
    rw [toNat_sub_le _ _ (by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48]
      omega), UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    omega
  have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
    rw [hsub 48 (by decide)]
    rfl
  have hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8 := by
    rw [hsub 40 (by decide)]
    rfl
  have hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16 := by
    rw [hsub 32 (by decide)]
    rfl
  have hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24 := by
    rw [hsub 24 (by decide)]
    rfl
  have hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32 := by
    rw [hsub 16 (by decide)]
    rfl
  have hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40 := by
    rw [hsub 8 (by decide)]
    rfl
  have hBaseBound : g0.toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase8Bound : (g0 + 48 - 40).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub40, Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase16Bound : (g0 + 48 - 32).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub32, Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase24Bound : (g0 + 48 - 24).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub24, Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase32Bound : (g0 + 48 - 16).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub16, Nat.mod_eq_of_lt (by omega)]
    omega
  have hBase40Bound : (g0 + 48 - 8).toNat % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
    rw [hsub8, Nat.mod_eq_of_lt (by omega)]
    omega
  rw [if_neg (Nat.not_lt.mpr hBaseBound),
    if_neg (Nat.not_lt.mpr hBase8Bound),
    if_neg (Nat.not_lt.mpr hBase16Bound),
    if_neg (Nat.not_lt.mpr hBase24Bound),
    if_neg (Nat.not_lt.mpr hBase32Bound),
    if_neg (Nat.not_lt.mpr hBase40Bound)]
  have hFinalFrame :
      { params := base.params,
        locals := ((((((((base.locals.set 67 (.i64 need)).set 68
          (.i64 previous)).set 69 (.i64 0)).set 70
          (.i64 capacity)).set 71 (.i64 next)).set 72 (.i64 0)).set 70
          (.i64 (g0 + 48 + need))).set 71
          (.i64 ((g0 + 48 + need - 1) / 65536 + 1))).set 72
          (.i64 (g0 + 48)) } =
        BookAllocSearch.bookAllocSearchFrame base need previous 0
          (g0 + 48 + need)
          ((g0 + 48 + need - 1) / 65536 + 1) (g0 + 48) := by
    unfold BookAllocSearch.bookAllocSearchFrame
    rw [hValues]
    congr 1
    apply List.ext_getElem?
    intro i
    by_cases h72 : 72 = i
    · subst i
      simp [List.getElem?_set]
    by_cases h71 : 71 = i
    · subst i
      simp [List.getElem?_set, h72]
    by_cases h70 : 70 = i
    · subst i
      simp [List.getElem?_set, h72, h71]
    · simp [List.getElem?_set, h72, h71, h70]
  rw [hFinalFrame]
  simpa only [bookAllocBumpStore, fixedArrayAllocBumpStore,
    fixedArrayHeaderMem,
    toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24, hsub16, hsub8]
    using hNext

theorem bookAllocBumpProg_skip
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (need previous current capacity next result : UInt64)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hResult : result ≠ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (BookAllocSearch.bookAllocSearchFrame base need previous current
        capacity next result) env) :
    wp «module» (bookAllocBumpProg ++ rest) Q st
      (BookAllocSearch.bookAllocSearchFrame base need previous current
        capacity next result) env := by
  simp only [bookAllocBumpProg, List.cons_append, List.nil_append,
    BookAllocSearch.bookAllocSearchFrame]
  wp_run_bump (hParams, hLocals, hValues)
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hResult])]
  simpa [BookAllocSearch.bookAllocSearchFrame, hValues] using hNext

theorem freshFixedArrayAt_fixedArrayAllocBumpStore
    (st : Store Unit) (g0 need stride : UInt64)
    (hNeed8 : 8 ≤ need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296) :
    FreshFixedArrayAt (fixedArrayAllocBumpStore st g0 need stride)
      (g0 + 48) need stride := by
  have hHeader := fixedArrayHeaderMem_spec st g0 need stride (by omega)
  unfold FreshFixedArrayAt at hHeader ⊢
  simpa only [fixedArrayAllocBumpStore] using hHeader

theorem freshOrderArrayAt_bookAllocBumpStore
    (st : Store Unit) (g0 need : UInt64)
    (hNeed8 : 8 ≤ need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296) :
    Allocation.FreshOrderArrayAt (bookAllocBumpStore st g0 need)
      (g0 + 48) need := by
  exact freshFixedArrayAt_fixedArrayAllocBumpStore st g0 need 5 hNeed8
    hFit32

theorem freeListAt_fixedArrayAllocBumpStore
    (st : Store Unit) (g0 need stride : UInt64) (nodes : List FreeNode)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hList : FreeListAt st.mem nodes) :
    FreeListAt (fixedArrayAllocBumpStore st g0 need stride).mem nodes := by
  let fresh : FreeNode := { root := g0 + 48, capacity := need }
  have hRootNat : fresh.root.toNat = g0.toNat + 48 := by
    unfold fresh
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    omega
  have hFresh48 : 48 ≤ fresh.root.toNat := by
    rw [hRootNat]
    omega
  have hFresh32 :
      fresh.root.toNat + fresh.capacity.toNat < 4294967296 := by
    rw [hRootNat]
    exact hFit32
  have hsep : ∀ node ∈ nodes,
      regionsDisjoint fresh.region node.region := by
    intro node hmem
    obtain ⟨hNode48, _, _⟩ := hList.mem_bounds hmem
    unfold regionsDisjoint FreeNode.region
    right
    rw [hRootNat]
    have hNodeBelow := hBelow node hmem
    omega
  have h1 := hList.frame_write64_disjoint
    (writer := fresh) (writeOffset := 48)
    (value := 5501223100278326855) hFresh48 hFresh32
    (by decide) (by decide) hsep
  have h2 := h1.frame_write64_disjoint
    (writer := fresh) (writeOffset := 40) (value := 1)
    hFresh48 hFresh32 (by decide) (by decide) hsep
  have h3 := h2.frame_write64_disjoint
    (writer := fresh) (writeOffset := 32) (value := need)
    hFresh48 hFresh32 (by decide) (by decide) hsep
  have h4 := h3.frame_write64_disjoint
    (writer := fresh) (writeOffset := 24) (value := 2)
    hFresh48 hFresh32 (by decide) (by decide) hsep
  have h5 := h4.frame_write64_disjoint
    (writer := fresh) (writeOffset := 16) (value := stride)
    hFresh48 hFresh32 (by decide) (by decide) hsep
  have h6 := h5.frame_write64_disjoint
    (writer := fresh) (writeOffset := 8) (value := 0)
    hFresh48 hFresh32 (by decide) (by decide) hsep
  have hsub (offset : UInt64) (hOffset : offset.toNat ≤ 48) :
      (g0 + 48 - offset).toNat =
        g0.toNat + 48 - offset.toNat := by
    rw [toNat_sub_le _ _ (by rw [hRootNat]; omega), hRootNat]
  have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
    rw [hsub 48 (by decide)]
    rfl
  have hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8 := by
    rw [hsub 40 (by decide)]
    rfl
  have hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16 := by
    rw [hsub 32 (by decide)]
    rfl
  have hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24 := by
    rw [hsub 24 (by decide)]
    rfl
  have hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32 := by
    rw [hsub 16 (by decide)]
    rfl
  have hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40 := by
    rw [hsub 8 (by decide)]
    rfl
  simpa only [fixedArrayAllocBumpStore, fixedArrayHeaderMem, fresh,
    toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24, hsub16, hsub8]
    using h6

theorem freeListAt_bookAllocBumpStore
    (st : Store Unit) (g0 need : UInt64) (nodes : List FreeNode)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hBelow : ∀ node ∈ nodes,
      node.root.toNat + node.capacity.toNat ≤ g0.toNat)
    (hList : FreeListAt st.mem nodes) :
    FreeListAt (bookAllocBumpStore st g0 need).mem nodes := by
  exact freeListAt_fixedArrayAllocBumpStore st g0 need 5 nodes hFit32
    hBelow hList

def bookAllocNoFitProg : Wasm.Program :=
  BookAllocSearch.bookAllocSearchProg ++ bookAllocBumpProg

theorem bookAllocNoFitProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (g0 need capacity next : UInt64) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hNeed8 : 8 ≤ need.toNat)
    (htop : (g0 + 48 + need).toNat =
      g0.toNat + 48 + need.toNat)
    (hFit32 : g0.toNat + 48 + need.toNat < 4294967296)
    (hFit : g0.toNat + 48 + need.toNat ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hList : FreeListAt st.mem nodes)
    (hNoFit : takeFirstFit need nodes = none)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous : UInt64,
      wp «module» rest Q (bookAllocBumpStore st g0 need)
        (BookAllocSearch.bookAllocSearchFrame base need previous 0
          (g0 + 48 + need)
          ((g0 + 48 + need - 1) / 65536 + 1) (g0 + 48)) env) :
    wp «module» (bookAllocNoFitProg ++ rest) Q st
      (BookAllocSearch.bookAllocSearchFrame base need 0 (freeHead nodes)
        capacity next 0) env := by
  unfold bookAllocNoFitProg
  rw [List.append_assoc]
  apply BookAllocSearch.bookAllocSearchProg_no_fit env st base need
    capacity next nodes hParams hLocals hValues hList hNoFit
  intro previous currentCapacity currentNext
  exact bookAllocBumpProg_spec env st base g0 need previous
    currentCapacity currentNext hParams hLocals hValues hNeed8 htop
    hFit32 hFit hPages hg0 Q rest (hNext previous)

end Project.ClobMatchFuel.BookAllocBump
