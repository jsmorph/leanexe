import Project.ClobLimit.Program
import Project.FixedArrayAllocation
import Project.ClobMatchFuel.AllocatorFrame
import Interpreter.Wasm.Wp.Tactic

/-!
# Empty trade-array allocation in `runMatch`

Function 18 executes the same empty stride-four fixed-array allocation twice
before it calls the internal matcher.  This module proves that instruction
block once and records its exact store and local frame for both uses.
-/

namespace Project.ClobLimit.RunMatchEmptyAlloc

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobMatchFuel.AllocatorFrame

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_alloc" "(" hParams:term "," hLocals:term "," hValues:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues)])

def prepareProg : Wasm.Program :=
  [
  .constI64 8,
  .constI64 0,
  .constI64 4,
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
  .localSet 36,
  .localGet 36,
  .constI64 8,
  .ltUI64,
  .iff 0 0 [
    .constI64 8,
    .localSet 36
  ] [],
  .constI64 0,
  .localSet 41,
  .constI64 0,
  .localSet 37,
  .globalGet 1,
  .localSet 38
]

def searchBodyProg : Wasm.Program :=
  [
  .localGet 38,
  .constI64 0,
  .eqI64,
  .br_if 1,
  .localGet 41,
  .constI64 0,
  .neI64,
  .br_if 1,
  .localGet 38,
  .constI64 32,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 39,
  .localGet 38,
  .constI64 8,
  .subI64,
  .wrapI64,
  .load64 0,
  .localSet 40,
  .localGet 39,
  .localGet 36,
  .geUI64,
  .iff 0 0 [
    .localGet 37,
    .constI64 0,
    .eqI64,
    .iff 0 0 [
      .localGet 40,
      .globalSet 1
    ] [
      .localGet 37,
      .constI64 8,
      .subI64,
      .wrapI64,
      .localGet 40,
      .store64 0
    ],
    .localGet 38,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 38,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 38,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 39,
    .store64 0,
    .localGet 38,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 38,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 4,
    .store64 0,
    .localGet 38,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0,
    .localGet 38,
    .localSet 41
  ] [
    .localGet 38,
    .localSet 37,
    .localGet 40,
    .localSet 38
  ],
  .br 0
]

def searchProg : Wasm.Program :=
  [.block 0 0 [.loop 0 0 searchBodyProg]]

def bumpProg : Wasm.Program :=
  [
  .localGet 41,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localGet 36,
    .addI64,
    .localSet 39,
    .localGet 39,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 39,
    .constI64 1,
    .subI64,
    .constI64 65536,
    .divUI64,
    .constI64 1,
    .addI64,
    .localSet 40,
    .memorySize,
    .extendUI32,
    .localGet 40,
    .ltUI64,
    .iff 0 0 [
      .localGet 40,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const 4294967295,
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 48,
    .addI64,
    .localSet 41,
    .localGet 39,
    .globalSet 0,
    .localGet 41,
    .constI64 48,
    .subI64,
    .wrapI64,
    .constI64 5501223100278326855,
    .store64 0,
    .localGet 41,
    .constI64 40,
    .subI64,
    .wrapI64,
    .constI64 1,
    .store64 0,
    .localGet 41,
    .constI64 32,
    .subI64,
    .wrapI64,
    .localGet 36,
    .store64 0,
    .localGet 41,
    .constI64 24,
    .subI64,
    .wrapI64,
    .constI64 2,
    .store64 0,
    .localGet 41,
    .constI64 16,
    .subI64,
    .wrapI64,
    .constI64 4,
    .store64 0,
    .localGet 41,
    .constI64 8,
    .subI64,
    .wrapI64,
    .constI64 0,
    .store64 0
  ] []
]

def finishProg : Wasm.Program :=
  [
  .globalGet 2,
  .constI64 1,
  .addI64,
  .globalSet 2,
  .localGet 41,
  .localSet 29,
  .localGet 29,
  .wrapI64,
  .constI64 0,
  .store64 0,
  .localGet 29,
  .localSet 13
]

def allocProg : Wasm.Program :=
  prepareProg ++ searchProg ++ bumpProg ++ finishProg

def prepareFrame (base : Locals) : Locals :=
  { base with
    locals := (((base.locals.set 29 (.i64 8)).set 34 (.i64 0)).set 30
      (.i64 0)).set 31 (.i64 0) }

def allocStore (st : Store Unit) (g0 g2 : UInt64) : Store Unit :=
  { st with
    globals := { globals :=
      (st.globals.globals.set 0 (.i64 (g0 + 56))).set 2 (.i64 (g2 + 1)) }
    mem := emptyFixedArrayMem st.mem g0 8 4 }

def allocFrame (base : Locals) (g0 : UInt64) : Locals :=
  { base with
    locals := (((((((((base.locals.set 29 (.i64 8)).set 34
      (.i64 0)).set 30 (.i64 0)).set 31 (.i64 0)).set 32
      (.i64 (g0 + 56))).set 33
      (.i64 ((g0 + 56 - 1) / 65536 + 1))).set 34
      (.i64 (g0 + 48))).set 22 (.i64 (g0 + 48))).set 6
      (.i64 (g0 + 48))) }

theorem allocStore_pages (st : Store Unit) (g0 g2 : UInt64) :
    (allocStore st g0 g2).mem.pages = st.mem.pages := by
  simp [allocStore, emptyFixedArrayMem, fixedArrayMem, fixedArrayHeaderMem,
    Mem.write64_pages]

theorem allocStore_global0
    (st : Store Unit) (g0 g2 : UInt64) (value : Value)
    (hGlobal0 : st.globals.globals[0]? = some value) :
    (allocStore st g0 g2).globals.globals[0]? =
      some (.i64 (g0 + 56)) := by
  have hLength := (List.getElem?_eq_some_iff.mp hGlobal0).1
  simp [allocStore, hLength]

theorem allocStore_global1
    (st : Store Unit) (g0 g2 value : UInt64)
    (hGlobal1 : st.globals.globals[1]? = some (.i64 value)) :
    (allocStore st g0 g2).globals.globals[1]? = some (.i64 value) := by
  have hLength := (List.getElem?_eq_some_iff.mp hGlobal1).1
  have hValue := (List.getElem?_eq_some_iff.mp hGlobal1).2
  simp [allocStore, hLength, hValue]

theorem allocStore_global2
    (st : Store Unit) (g0 g2 : UInt64) (value : Value)
    (hGlobal2 : st.globals.globals[2]? = some value) :
    (allocStore st g0 g2).globals.globals[2]? =
      some (.i64 (g2 + 1)) := by
  have hLength := (List.getElem?_eq_some_iff.mp hGlobal2).1
  simp [allocStore, hLength]

theorem allocStore_bytes_before
    (st : Store Unit) (g0 g2 : UInt64) (a : Nat)
    (hFit32 : g0.toNat + 56 < 4294967296) (ha : a < g0.toNat) :
    (allocStore st g0 g2).mem.bytes a = st.mem.bytes a := by
  exact emptyFixedArrayMem_bytes_before st.mem g0 8 4 a hFit32 ha

theorem allocStore_empty_trade
    (st : Store Unit) (g0 g2 : UInt64)
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536) :
    OwnedTradeArrayAt (allocStore st g0 g2) (g0 + 48) 8 [] := by
  have hRoot : (g0 + 48).toNat = g0.toNat + 48 :=
    fixedArrayBumpRoot_toNat g0 (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      rw [hSize]
      omega)
  have hAlloc := emptyFixedArrayMem_spec st g0 8 4 hFit32
  refine ⟨?_, ?_⟩
  · change FreshFixedArrayAt (allocStore st g0 g2) (g0 + 48) 8 4
    have hFresh := hAlloc.1
    unfold FreshFixedArrayAt at hFresh ⊢
    simpa [allocStore] using hFresh
  · unfold TradesAt
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← toUInt32_eq_ofNat]
      simpa [allocStore] using hAlloc.2
    · rw [allocStore_pages, hRoot, Nat.mod_eq_of_lt (by omega)]
      omega
    · intro j hj
      simp at hj

theorem ownedOrderArrayAt_allocStore
    {st : Store Unit} {g0 g2 source sourceCapacity : UInt64}
    {os : List OrderL}
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hCapacity : fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os) :
    OwnedOrderArrayAt (allocStore st g0 g2) source sourceCapacity os := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (allocStore st g0 g2).mem.bytes a = st.mem.bytes a := by
    intro a _ haHigh
    exact allocStore_bytes_before st g0 g2 a hFit32 (by omega)
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    OrdersAt.frame_region hSource32 hSource48 hCapacity
      (allocStore_pages st g0 g2) hBytes hOwned.2⟩

theorem ownedTradeArrayAt_allocStore
    {st : Store Unit} {g0 g2 source sourceCapacity : UInt64}
    {ts : List TradeL}
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes ts.length 4 < 4294967296)
    (hCapacity : fixedArrayBytes ts.length 4 ≤ sourceCapacity.toNat)
    (hBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hOwned : OwnedTradeArrayAt st source sourceCapacity ts) :
    OwnedTradeArrayAt (allocStore st g0 g2) source sourceCapacity ts := by
  have hBytes : ∀ a : Nat,
      source.toNat - 48 ≤ a → a < source.toNat + sourceCapacity.toNat →
        (allocStore st g0 g2).mem.bytes a = st.mem.bytes a := by
    intro a _ haHigh
    exact allocStore_bytes_before st g0 g2 a hFit32 (by omega)
  exact ⟨hOwned.1.frame_region (by omega) hSource48 hBytes,
    TradesAt.frame_region hSource32 hSource48 hCapacity
      (allocStore_pages st g0 g2) hBytes hOwned.2⟩

set_option Elab.async false in
theorem allocProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (g0 g2 : UInt64)
    (hParams : base.params.length = 7)
    (hLocals : base.locals.length = 35)
    (hValues : base.values = [])
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q (allocStore st g0 g2)
      (allocFrame base g0) env) :
    wp «module» (allocProg ++ rest) Q st base env := by
  simp only [allocProg, prepareProg, searchProg, bumpProg,
    finishProg, List.cons_append, List.nil_append]
  wp_run_alloc (hParams, hLocals, hValues)
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_alloc (hParams, hLocals, hValues)
  simp only [hg1]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = prepareFrame base)
    (μ := fun _ _ => 0)
  · refine ⟨rfl, ?_⟩
    simp [prepareFrame, hValues]
  · rintro st1 s1 ⟨hSt, hFrame⟩
    subst st1
    subst s1
    simp only [searchBodyProg, prepareFrame]
    wp_run_alloc (hParams, hLocals, hValues)
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run_alloc (hParams, hLocals, hValues)
    simp only [hg0]
    have hTop : (g0 + 48 + 8).toNat = g0.toNat + 56 := by
      rw [UInt64.toNat_add, UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      have h8 : (8 : UInt64).toNat = 8 := rfl
      rw [h48, h8]
      omega
    have hNoWrap : ¬g0 + 48 + 8 < g0 := by
      rw [UInt64.lt_iff_toNat_lt, hTop]
      omega
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hNoWrap])]
    wp_run_alloc (hParams, hLocals, hValues)
    have hNoGrow := fixedArrayBump_no_grow g0 8 st.mem.pages
      (by simpa using hTop) (by simpa using hFit) hPages
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simpa using hNoGrow)]
    wp_run_alloc (hParams, hLocals, hValues)
    simp only [hg0]
    try wp_run_alloc (hParams, hLocals, hValues)
    try simp
    have hRoot : (g0 + 48).toNat = g0.toNat + 48 :=
      fixedArrayBumpRoot_toNat g0 (by
        have hSize : UInt64.size = 18446744073709551616 := rfl
        rw [hSize]
        omega)
    have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
      have h := fixedArrayBumpRoot_sub_toNat g0 48 hRoot (by decide)
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48] at h
      simpa only [Nat.add_sub_cancel] using h
    have hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8 := by
      simpa using fixedArrayBumpRoot_sub_toNat g0 40 hRoot (by decide)
    have hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16 := by
      simpa using fixedArrayBumpRoot_sub_toNat g0 32 hRoot (by decide)
    have hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24 := by
      simpa using fixedArrayBumpRoot_sub_toNat g0 24 hRoot (by decide)
    have hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32 := by
      simpa using fixedArrayBumpRoot_sub_toNat g0 16 hRoot (by decide)
    have hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40 := by
      simpa using fixedArrayBumpRoot_sub_toNat g0 8 hRoot (by decide)
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
    simp only [hg2]
    have hRootBound : ¬st.mem.pages * 65536 <
        (g0.toNat + 48) % 4294967296 + 8 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_neg hRootBound]
    have hTopValue : g0 + 48 + 8 = g0 + 56 := by
      rw [UInt64.add_assoc]
      rw [show (48 : UInt64) + 8 = 56 by decide]
    simpa only [allocStore, allocFrame, emptyFixedArrayMem, fixedArrayMem,
      fixedArrayHeaderMem, toUInt32_eq_ofNat, hsub48, hsub40, hsub32,
      hsub24, hsub16, hsub8, hTopValue, hValues] using hNext

end Project.ClobLimit.RunMatchEmptyAlloc
