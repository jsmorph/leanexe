import Project.ClobDepth.Func3

/-!
# Empty level-array allocation in function 6

Function 6 executes the same empty stride-two fixed-array allocation twice
before it folds the orders.  This module proves that instruction block once
and records its exact store and local frame for both uses.  The slice leaves
the allocated root on the stack for the caller's destination local.
-/

namespace Project.ClobDepth.Func6Alloc

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_alloc" "(" hParams:term "," hLocals:term ","
    hValues:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues)])

def prepareFrame (base : Locals) : Locals :=
  { base with
    locals := (((base.locals.set 28 (.i64 8)).set 33 (.i64 0)).set 29
      (.i64 0)).set 30 (.i64 0) }

def allocStore (st : Store Unit) (g0 g2 : UInt64) : Store Unit :=
  { st with
    globals := { globals :=
      (st.globals.globals.set 0 (.i64 (g0 + 56))).set 2 (.i64 (g2 + 1)) }
    mem := emptyFixedArrayMem st.mem g0 8 2 }

def allocFrame (base : Locals) (g0 : UInt64) : Locals :=
  { base with
    locals := (((((((((base.locals.set 28 (.i64 8)).set 33
      (.i64 0)).set 29 (.i64 0)).set 30 (.i64 0)).set 31
      (.i64 (g0 + 56))).set 32
      (.i64 ((g0 + 56 - 1) / 65536 + 1))).set 33
      (.i64 (g0 + 48))).set 23 (.i64 (g0 + 48))).set 0
      (.i64 (g0 + 48)))
    values := [.i64 (g0 + 48)] }

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
  exact emptyFixedArrayMem_bytes_before st.mem g0 8 2 a hFit32 ha

theorem allocStore_empty_levels
    (st : Store Unit) (g0 g2 : UInt64)
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536) :
    OwnedLevelArrayAt (allocStore st g0 g2) (g0 + 48) 8 [] := by
  have hRoot : (g0 + 48).toNat = g0.toNat + 48 :=
    fixedArrayBumpRoot_toNat g0 (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      rw [hSize]
      omega)
  have hAlloc := emptyFixedArrayMem_spec st g0 8 2 hFit32
  refine ⟨?_, ?_⟩
  · have hFresh := hAlloc.1
    unfold FreshFixedArrayAt at hFresh ⊢
    simpa [allocStore] using hFresh
  · unfold LevelsAt
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← toUInt32_eq_ofNat]
      simpa [allocStore] using hAlloc.2
    · rw [allocStore_pages, hRoot, Nat.mod_eq_of_lt (by omega)]
      omega
    · intro j hj
      simp at hj

set_option Elab.async false in
theorem allocProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (g0 g2 : UInt64)
    (hParams : base.params.length = 3)
    (hLocals : base.locals.length = 43)
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
    wp «module» (Entry.func6AllocProg ++ rest) Q st base env := by
  simp only [Entry.func6AllocProg, List.cons_append, List.nil_append]
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
    simp only [prepareFrame]
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

end Project.ClobDepth.Func6Alloc
